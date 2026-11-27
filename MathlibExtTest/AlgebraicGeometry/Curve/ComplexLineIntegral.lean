/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.ComplexLineIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.FieldTheory.RatFunc.IntermediateField
import MathlibExt.AlgebraicGeometry.Curve.IsCurveOver
import MathlibExt.AlgebraicGeometry.Curve.OrdEqNegLog
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceClassification
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceInftyDeg
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceInftyOrd
import MathlibExt.RingTheory.Kaehler.Transcendental

@[expose] public section

open scoped Manifold Topology

namespace AlgebraicCurve

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [IsCurveOver ℂ F]

-- The coordinate differential at a place is the differential of the uniformizer, which has order
-- one there.
example (v : Place ℂ F) : v.dCoord = KaehlerDifferential.D ℂ F v.uniformizer := rfl

example (v : Place ℂ F) : v.ord v.uniformizer = 1 := v.ord_uniformizer

-- Every place of a complex curve is rational, and evaluation there takes the residue.
example (v : Place ℂ F) : v.IsRational := v.isRational_of_isCurveOver

example (v : Place ℂ F) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.HasValueAt f (v.evalAt v.isRational_of_isCurveOver f) :=
  v.hasValueAt_evalAt _ hf

-- Without holomorphic preferred charts, neither differentials nor primitives can be read.
example [∀ v : Place ℂ F, v.DCoordGenerates] (_v : Place ℂ F) (_ω : Ω[F⁄ℂ])
    (_γ : Path _v _v) : True := by
  fail_if_success have := _v.readDifferential _ω
  fail_if_success have := IsPrimitiveAlong _ω _γ fun _ => 0
  trivial

variable [IsHolomorphicAtlas F]

-- A function regular at a place reads analytically at the centre of the chart at that place, and
-- the uniformizer reads with nonzero derivative there.
example (v : Place ℂ F) {f : F} (hf : f ∈ v.toValuationSubring) :
    AnalyticAt ℂ (v.chartRead f) (extChartAt 𝓘(ℂ, ℂ) v v) :=
  v.analyticAt_chartRead hf

example (v : Place ℂ F) : deriv (v.chartRead v.uniformizer) (extChartAt 𝓘(ℂ, ℂ) v v) ≠ 0 :=
  IsHolomorphicAtlas.deriv_chartRead_uniformizer_ne_zero v

variable [∀ v : Place ℂ F, v.DCoordGenerates]

-- The differential `f • dCoord` reads as the reading of `f` times the derivative of the reading
-- of the uniformizer, and the zero differential reads as zero.
example (v : Place ℂ F) (f : F) (z : ℂ) :
    v.readDifferential (f • v.dCoord) z =
      v.chartRead f z * deriv (v.chartRead v.uniformizer) z := by
  unfold Place.readDifferential
  rw [v.differentialCoeff_unique rfl]

example (v : Place ℂ F) (z : ℂ) : v.readDifferential 0 z = 0 := by
  simp

-- The zero differential has order zero, not an infinite order of vanishing.
example (v : Place ℂ F) : v.ordDifferential (0 : Ω[F⁄ℂ]) = 0 :=
  v.ordDifferential_zero

-- The line integral is the increment of any primitive, so a primitive with distinct end values
-- gives a nonzero integral.
example (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) (g : unitInterval → ℂ)
    (hg : IsPrimitiveAlong ω γ g) : pathIntegral ω γ ⟨g, hg⟩ = g 1 - g 0 := by
  unfold pathIntegral
  exact (⟨g, hg⟩ : ∃ g, IsPrimitiveAlong ω γ g).choose_spec.sub_eq_sub hg

example (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) (g : unitInterval → ℂ)
    (hg : IsPrimitiveAlong ω γ g) (h01 : g 1 ≠ g 0) : pathIntegral ω γ ⟨g, hg⟩ ≠ 0 := by
  rw [hg.pathIntegral_eq]
  exact sub_ne_zero.mpr h01

-- From chart readings to the integral: if the path stays in one preferred chart `e`, the reading
-- of `ω` there is the constant `1`, and the path runs from the place with coordinate `0` to the
-- place with coordinate `1`, then the coordinate is a primitive and the integral is `1`.
example (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) (e : OpenPartialHomeomorph (Place ℂ F) ℂ)
    (he : ∀ t, chartAt ℂ (γ t) = e)
    (h1 : ∀ t, ∀ᶠ z in 𝓝 (e (γ t)), (γ t).readDifferential ω z = 1)
    (hP : e P = 0) (hQ : e Q = 1) :
    ∃ h : IsPrimitiveAlong ω γ (fun t => e (γ t)), pathIntegral ω γ ⟨_, h⟩ = 1 := by
  have hΦ : ∀ t, ∀ᶠ z in 𝓝 (e (γ t)), HasDerivAt id ((γ t).readDifferential ω z) z :=
    fun t => (h1 t).mono fun z hz => by
      rw [hz]
      exact hasDerivAt_id z
  have hprim : IsPrimitiveAlong ω γ (fun t => e (γ t)) := isPrimitiveAlong_of_chartAt_eq he hΦ
  refine ⟨hprim, ?_⟩
  unfold pathIntegral
  rw [(⟨_, hprim⟩ : ∃ g, IsPrimitiveAlong ω γ g).choose_spec.sub_eq_sub hprim]
  simp only [Path.source, Path.target, hP, hQ, sub_zero]

example (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) (e : OpenPartialHomeomorph (Place ℂ F) ℂ)
    (he : ∀ t, chartAt ℂ (γ t) = e) (Φ : ℂ → ℂ)
    (hΦ : ∀ t, ∀ᶠ z in 𝓝 (e (γ t)), HasDerivAt Φ ((γ t).readDifferential ω z) z) :
    pathIntegral ω γ ⟨_, isPrimitiveAlong_of_chartAt_eq he hΦ⟩ = Φ (e Q) - Φ (e P) :=
  pathIntegral_eq_sub_of_chartAt_eq he hΦ _

-- Reversal changes the sign of the increment, and concatenation adds increments.
example (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) (g : unitInterval → ℂ)
    (hg : IsPrimitiveAlong ω γ g) : pathIntegral ω γ.symm ⟨_, hg.symm⟩ = g 0 - g 1 := by
  rw [hg.symm.pathIntegral_eq, Function.comp_apply, Function.comp_apply, unitInterval.symm_one,
    unitInterval.symm_zero]

example (ω : Ω[F⁄ℂ]) {P Q R : Place ℂ F} (γ : Path P Q) (γ' : Path Q R)
    (g g' : unitInterval → ℂ) (hg : IsPrimitiveAlong ω γ g) (hg' : IsPrimitiveAlong ω γ' g')
    (h : ∃ k, IsPrimitiveAlong ω (γ.trans γ') k) :
    pathIntegral ω (γ.trans γ') h = (g 1 - g 0) + (g' 1 - g' 0) := by
  rw [pathIntegral_trans ⟨g, hg⟩ ⟨g', hg'⟩ h, hg.pathIntegral_eq, hg'.pathIntegral_eq]

-- Going along a path and back gives the integral zero.
example (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) (h : ∃ g, IsPrimitiveAlong ω γ g)
    (h' : ∃ g, IsPrimitiveAlong ω (γ.trans γ.symm) g) :
    pathIntegral ω (γ.trans γ.symm) h' = 0 := by
  rw [pathIntegral_trans h (exists_isPrimitiveAlong_symm h) h', pathIntegral_symm h,
    add_neg_cancel]

-- Boundary examples: the zero differential along any path, and any differential along a constant
-- path, have zero integral.
example {P Q : Place ℂ F} (γ : Path P Q) : pathIntegral 0 γ ⟨0, isPrimitiveAlong_zero γ⟩ = 0 :=
  pathIntegral_zero γ _

example (ω : Ω[F⁄ℂ]) (P : Place ℂ F) (h : ∃ g, IsPrimitiveAlong ω (Path.refl P) g) :
    pathIntegral ω (Path.refl P) h = 0 :=
  pathIntegral_refl ω P h

-- The Abel-Jacobi vector collects the line integrals of the family, and vanishes for the zero
-- family.
example {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) {P₀ P : Place ℂ F} (γ : Path P₀ P)
    (h : ∀ i, ∃ g, IsPrimitiveAlong (b i) γ g) (i : Fin n) :
    abelJacobiVec b γ h i = pathIntegral (b i) γ (h i) :=
  rfl

example {n : ℕ} {P₀ P : Place ℂ F} (γ : Path P₀ P)
    (h : ∀ i, ∃ g, IsPrimitiveAlong ((fun _ : Fin n => (0 : Ω[F⁄ℂ])) i) γ g) :
    abelJacobiVec (fun _ : Fin n => (0 : Ω[F⁄ℂ])) γ h = 0 :=
  abelJacobiVec_zero γ h

-- A loop gives a period, and two paths with the same endpoints differ by a period.
example {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) {P : Place ℂ F} (γ : Path P P)
    (h : ∀ i, ∃ g, IsPrimitiveAlong (b i) γ g) : abelJacobiVec b γ h ∈ periodSubgroup b :=
  AddSubgroup.subset_closure ⟨P, γ, h, rfl⟩

example {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) {P₀ P : Place ℂ F} (γ γ' : Path P₀ P)
    (h : ∀ i, ∃ g, IsPrimitiveAlong (b i) γ g) (h' : ∀ i, ∃ g, IsPrimitiveAlong (b i) γ' g) :
    abelJacobiVec b γ h - abelJacobiVec b γ' h' ∈ periodSubgroup b :=
  abelJacobiVec_sub_mem_periodSubgroup b γ γ' h h'

-- The Abel-Jacobi map sends a multiple of a place to the multiple of its Abel-Jacobi vector, and
-- other choices of paths change it by a period.
example {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) {P₀ : Place ℂ F} (γ : ∀ P, Path P₀ P)
    (h : ∀ P i, ∃ g, IsPrimitiveAlong (b i) (γ P) g) (v : Place ℂ F) (m : ℤ) :
    abelJacobiDiv b γ h (Finsupp.single v m) = m • abelJacobiVec b (γ v) (h v) := by
  simp [abelJacobiDiv]

example {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) {P₀ : Place ℂ F} (γ γ' : ∀ P, Path P₀ P)
    (h : ∀ P i, ∃ g, IsPrimitiveAlong (b i) (γ P) g)
    (h' : ∀ P i, ∃ g, IsPrimitiveAlong (b i) (γ' P) g) (D : Divisor ℂ F) :
    abelJacobiDiv b γ h D - abelJacobiDiv b γ' h' D ∈ periodSubgroup b :=
  abelJacobiDiv_sub_mem_periodSubgroup b γ γ' h h' D

end AlgebraicCurve

/-! ## A concrete curve: the complex projective line

The places of `ℂ(X)` are the points `a` of `ℂ` and the place at infinity. The affine coordinate
charts the places other than infinity, and the inverse coordinate charts the places other than `0`.
With these charts `ℂ(X)` is a curve with holomorphic preferred charts. Near every finite place, the
local reading of `dX`, computed from residue evaluation and the differential formula, is `1`, so the
affine coordinate is a primitive of `dX` and the line integral of `dX` from the place `0` to the
place `1` is `1`. This is test scaffolding: the declarations are private and the instances local.
-/

namespace AlgebraicCurve.ComplexLineIntegralTest

noncomputable section

open AlgebraicCurve.RationalFunctionField Polynomial IsDedekindDomain WithZero

@[instance_reducible]
private noncomputable def decEqRatFunc : DecidableEq (RatFunc ℂ) := Classical.decEq _

attribute [local instance] decEqRatFunc

local notation "pt" => placeOfPoint ℂ
local notation "∞ₚ" => placeInfty ℂ
local notation "wpt" a:max => heightOneSpectrumOfIrreducible ℂ (irreducible_X_sub_C a)
local notation "rf" => algebraMap ℂ[X] (RatFunc ℂ)

private theorem mem_wpt_iff (a : ℂ) (p : ℂ[X]) : p ∈ (wpt a).asIdeal ↔ p.eval a = 0 := by
  rw [heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton, dvd_iff_isRoot]
  rfl

private theorem algebraMap_C (c : ℂ) : algebraMap ℂ (RatFunc ℂ) c = rf (C c) := by
  rw [IsScalarTower.algebraMap_apply ℂ ℂ[X] (RatFunc ℂ), Polynomial.algebraMap_eq]

private theorem hasValueAt_pt_rf (a : ℂ) (p : ℂ[X]) : (pt a).HasValueAt (rf p) (p.eval a) := by
  have hmem : p - C (p.eval a) ∈ (wpt a).asIdeal := by
    rw [mem_wpt_iff]
    simp
  have hO : rf (p - C (p.eval a)) ∈ (pt a).toValuationSubring :=
    algebraMap_mem_ofHeightOneSpectrum ℂ (wpt a) _
  have hlt : (pt a).adicValuation (rf (p - C (p.eval a))) < 1 :=
    (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := ℂ) (F := RatFunc ℂ)
      (wpt a)).lt_one_iff_lt_one.mp
        ((HeightOneSpectrum.valuation_lt_one_iff_mem (wpt a) _).mpr hmem)
  have hmax : (⟨_, hO⟩ : (pt a).toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    ((pt a).mem_maximalIdeal_iff_adicValuation_lt_one _).mpr hlt
  change rf p - algebraMap ℂ (RatFunc ℂ) (p.eval a) ∈ (pt a).toValuationSubring.nonunits
  rw [algebraMap_C, ← map_sub]
  exact ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.mem_maximalIdeal _).mp hmax)

private theorem hasValueAt_pt_div (a : ℂ) {p q : ℂ[X]} (hq : q.eval a ≠ 0) :
    (pt a).HasValueAt (rf p / rf q) (p.eval a / q.eval a) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact (pt a).hasValueAt_mul (hasValueAt_pt_rf a p)
    ((pt a).hasValueAt_inv (hasValueAt_pt_rf a q) hq)

private theorem evalAt_eq_of_hasValueAt {v : Place ℂ (RatFunc ℂ)} (hv : v.IsRational)
    {f : RatFunc ℂ} {c : ℂ} (h : v.HasValueAt f c) : v.evalAt hv f = c :=
  v.hasValueAt_unique (v.hasValueAt_evalAt hv (v.mem_of_hasValueAt h)) h

/-- The order at `pt a` of a nonzero polynomial is minus the log of its intValuation. -/
private theorem ord_pt_rf (a : ℂ) {p : ℂ[X]} (hp : p ≠ 0) :
    (pt a).ord (rf p) = -log ((wpt a).intValuation p) := by
  have hw : ((wpt a).valuation (RatFunc ℂ)).valuationSubring = (pt a).toValuationSubring := rfl
  have hπ : (wpt a).valuation (RatFunc ℂ) (rf (X - C a)) = exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (wpt a).intValuation_singleton (X_sub_C_ne_zero a) rfl
  rw [(pt a).ord_eq_neg_log_of_valuationSubring_eq _ hw hπ (RatFunc.algebraMap_ne_zero hp),
    HeightOneSpectrum.valuation_of_algebraMap]

private theorem ord_pt_X_sub_C (a b : ℂ) : (pt a).ord (rf (X - C b)) = if b = a then 1 else 0 := by
  rw [ord_pt_rf a (X_sub_C_ne_zero b)]
  split_ifs with h
  · subst h
    rw [(wpt b).intValuation_singleton (X_sub_C_ne_zero b) rfl, log_exp, neg_neg]
  · have hnot : X - C b ∉ (wpt a).asIdeal := by
      rw [mem_wpt_iff]
      simpa [sub_eq_zero] using fun h' => h h'.symm
    rw [HeightOneSpectrum.intValuation_eq_one_iff.mpr hnot, log_one, neg_zero]

private theorem ord_inf_X_sub_C (b : ℂ) : (∞ₚ).ord (rf (X - C b)) = -1 := by
  rw [ord_placeInfty (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero b)),
    RatFunc.intDegree_polynomial, natDegree_X_sub_C]
  rfl

/-! ### The rational function field is a curve -/

private noncomputable def divXSubC (b : ℂ) : Divisor ℂ (RatFunc ℂ) :=
  Finsupp.single (pt b) 1 - Finsupp.single ∞ₚ 1

private theorem pt_ne_inf (a : ℂ) : pt a ≠ ∞ₚ := placeOfPoint_ne_placeInfty ℂ a

private theorem divXSubC_apply (b : ℂ) (v : Place ℂ (RatFunc ℂ)) :
    divXSubC b v = v.ord (rf (X - C b)) := by
  classical
  rcases eq_placeOfPoint_or_eq_placeInfty ℂ v with ⟨a, rfl⟩ | rfl
  · rw [ord_pt_X_sub_C, divXSubC, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply,
      ite_eq_right (Ne.symm (pt_ne_inf a)), sub_zero]
    by_cases h : b = a
    · subst h; simp
    · rw [ite_eq_right (fun h' => h (placeOfPoint_injective ℂ h')), ite_eq_right h]
  · rw [ord_inf_X_sub_C, divXSubC, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply,
      ite_eq_right (pt_ne_inf b), ite_eq_left rfl]
    norm_num

private theorem degree_divXSubC (b : ℂ) : Divisor.degree (divXSubC b) = 0 := by
  rw [divXSubC, map_sub, Divisor.degree_single, Divisor.degree_single, deg_placeOfPoint,
    deg_placeInfty]
  norm_num

private noncomputable def divPoly (p : ℂ[X]) : Divisor ℂ (RatFunc ℂ) := (p.roots.map divXSubC).sum

private theorem ord_rf_multiset_prod (v : Place ℂ (RatFunc ℂ)) (s : Multiset ℂ) :
    v.ord (rf (s.map (fun b => X - C b)).prod) = (s.map fun b => v.ord (rf (X - C b))).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [v.ord_one]
  | cons b s ih =>
    have hb : rf (X - C b) ≠ 0 := RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero b)
    have hs : rf (s.map (fun b => X - C b)).prod ≠ 0 := by
      refine RatFunc.algebraMap_ne_zero ?_
      exact Multiset.prod_ne_zero (by simp [X_sub_C_ne_zero])
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, v.ord_mul hb hs, ih, Multiset.map_cons,
      Multiset.sum_cons]

private theorem divPoly_apply {p : ℂ[X]} (hp : p ≠ 0) (v : Place ℂ (RatFunc ℂ)) :
    divPoly p v = v.ord (rf p) := by
  have hsplit := (IsAlgClosed.splits p).eq_prod_roots
  have hc : rf (C p.leadingCoeff) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (by simpa using leadingCoeff_ne_zero.mpr hp)
  have hs : rf (p.roots.map (fun b => X - C b)).prod ≠ 0 := by
    refine RatFunc.algebraMap_ne_zero ?_
    exact Multiset.prod_ne_zero (by simp [X_sub_C_ne_zero])
  conv_rhs => rw [hsplit]
  rw [map_mul, v.ord_mul hc hs, ← algebraMap_C, v.ord_algebraMap, zero_add,
    ord_rf_multiset_prod, divPoly]
  rw [← Finsupp.applyAddHom_apply, map_multiset_sum, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun b _ => ?_
  simp [divXSubC_apply]

private theorem degree_divPoly (p : ℂ[X]) : Divisor.degree (divPoly p) = 0 := by
  rw [divPoly, map_multiset_sum, Multiset.map_map]
  simp [degree_divXSubC]

private theorem exists_divisor_ratFunc (f : RatFunc ℂ) (hf : f ≠ 0) :
    ∃ D : Divisor ℂ (RatFunc ℂ), (∀ v, D v = v.ord f) ∧ Divisor.degree D = 0 := by
  have hn : f.num ≠ 0 := fun h => hf (RatFunc.num_eq_zero_iff.mp h)
  have hd : f.denom ≠ 0 := f.denom_ne_zero
  refine ⟨divPoly f.num - divPoly f.denom, fun v => ?_, ?_⟩
  · have hrn : rf f.num ≠ 0 := RatFunc.algebraMap_ne_zero hn
    have hrd : (rf f.denom)⁻¹ ≠ 0 := inv_ne_zero (RatFunc.algebraMap_ne_zero hd)
    conv_rhs => rw [← f.num_div_denom, div_eq_mul_inv]
    rw [Finsupp.sub_apply, divPoly_apply hn, divPoly_apply hd, v.ord_mul hrn hrd, v.ord_inv,
      sub_eq_add_neg]
  · rw [map_sub, degree_divPoly, degree_divPoly, sub_zero]

private theorem isSeparable_adjoin_X :
    Algebra.IsSeparable (IntermediateField.adjoin ℂ ({RatFunc.X} : Set (RatFunc ℂ)))
      (RatFunc ℂ) := by
  refine ⟨fun x => ?_⟩
  have hx : x ∈ IntermediateField.adjoin ℂ ({RatFunc.X} : Set (RatFunc ℂ)) := by
    rw [RatFunc.adjoin_X]
    trivial
  exact isSeparable_algebraMap
    (F := IntermediateField.adjoin ℂ ({RatFunc.X} : Set (RatFunc ℂ))) (K := RatFunc ℂ) ⟨x, hx⟩

attribute [local instance] isSeparable_adjoin_X

private noncomputable def kaehlerBasis : Module.Basis Unit (RatFunc ℂ) Ω[(RatFunc ℂ)⁄ℂ] :=
  Module.Basis.mk (v := fun _ => KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X)
    (linearIndependent_unique_iff.mpr
      (KaehlerDifferential.D_ne_zero_of_transcendental ℂ _ RatFunc.transcendental_X))
    (by
      rw [Set.range_const, KaehlerDifferential.span_D_eq_top_of_transcendental ℂ _
        RatFunc.transcendental_X])

private theorem kaehlerBasis_apply (u : Unit) :
    kaehlerBasis u = KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X := by
  simp [kaehlerBasis]

private theorem finiteResidue_ratFunc (v : Place ℂ (RatFunc ℂ)) :
    Module.Finite ℂ (IsLocalRing.ResidueField v.toValuationSubring) := by
  have h : v.deg = 1 := by
    rcases eq_placeOfPoint_or_eq_placeInfty ℂ v with ⟨a, rfl⟩ | rfl
    · exact deg_placeOfPoint ℂ a
    · exact deg_placeInfty ℂ
  exact Module.finite_of_finrank_eq_succ (n := 0) h

private theorem isCurveOver_ratFunc : IsCurveOver ℂ (RatFunc ℂ) where
  finiteResidue := finiteResidue_ratFunc
  exists_divisor := exists_divisor_ratFunc
  kaehler_free_rank_one :=
    ⟨Module.Free.of_basis kaehlerBasis, (Module.finrank_eq_card_basis kaehlerBasis).trans (by simp)⟩

attribute [local instance] isCurveOver_ratFunc

/-! ### The derivative with respect to `X` -/

/-- The coefficient of a differential with respect to `D X`, as a derivation. -/
private noncomputable def derivX : Derivation ℂ (RatFunc ℂ) (RatFunc ℂ) :=
  (kaehlerBasis.coord ()).compDer (KaehlerDifferential.D ℂ (RatFunc ℂ))

private theorem derivX_apply (f : RatFunc ℂ) :
    derivX f = kaehlerBasis.coord () (KaehlerDifferential.D ℂ (RatFunc ℂ) f) :=
  rfl

private theorem D_eq_derivX_smul (f : RatFunc ℂ) :
    KaehlerDifferential.D ℂ (RatFunc ℂ) f =
      derivX f • KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X := by
  have h := kaehlerBasis.sum_repr (KaehlerDifferential.D ℂ (RatFunc ℂ) f)
  rw [Fintype.sum_unique, kaehlerBasis_apply] at h
  rw [derivX_apply, Module.Basis.coord_apply]
  exact h.symm

private theorem D_X_ne_zero : KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X ≠ 0 :=
  KaehlerDifferential.D_ne_zero_of_transcendental ℂ _ RatFunc.transcendental_X

private theorem derivX_X : derivX RatFunc.X = 1 := by
  have h := D_eq_derivX_smul RatFunc.X
  have h1 : (1 : RatFunc ℂ) • KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X
      = derivX RatFunc.X • KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X := by
    rw [one_smul]
    exact h
  exact (smul_left_injective (RatFunc ℂ) D_X_ne_zero h1).symm

private theorem aeval_X_ratFunc (p : ℂ[X]) : aeval (RatFunc.X : RatFunc ℂ) p = rf p := by
  rw [← RatFunc.algebraMap_X, aeval_algebraMap_apply]
  simp

private theorem derivX_rf (p : ℂ[X]) : derivX (rf p) = rf (derivative p) := by
  rw [← aeval_X_ratFunc, Derivation.map_aeval, derivX_X, smul_eq_mul, mul_one, aeval_X_ratFunc]

private theorem derivX_div (p q : ℂ[X]) :
    derivX (rf p / rf q) = rf (q * derivative p - p * derivative q) / rf (q ^ 2) := by
  rw [Derivation.leibniz_div, derivX_rf, derivX_rf, smul_eq_mul, smul_eq_mul, smul_eq_mul, map_sub,
    map_mul, map_mul, map_pow, div_eq_mul_inv, inv_pow, mul_comm]

private theorem eq_algebraMap_of_derivX_eq_zero {f : RatFunc ℂ} (hf : derivX f = 0) :
    ∃ c : ℂ, f = algebraMap ℂ (RatFunc ℂ) c := by
  set p := f.num
  set q := f.denom
  have hq : q ≠ 0 := f.denom_ne_zero
  have hfpq : f = rf p / rf q := f.num_div_denom.symm
  rw [hfpq, derivX_div] at hf
  have hq2 : rf (q ^ 2) ≠ 0 := RatFunc.algebraMap_ne_zero (pow_ne_zero 2 hq)
  have hnum : q * derivative p - p * derivative q = 0 := by
    rw [div_eq_zero_iff, or_iff_left hq2] at hf
    exact RatFunc.algebraMap_injective ℂ (by rw [hf, map_zero])
  have hcop : IsCoprime p q := f.isCoprime_num_denom
  have hdvd : q ∣ derivative q := by
    have h1 : q ∣ p * derivative q := ⟨derivative p, by linear_combination -hnum⟩
    exact hcop.symm.dvd_of_dvd_mul_left h1
  have hq0 : q.natDegree = 0 := by
    by_contra hne
    have hdq : derivative q ≠ 0 := by
      intro h0
      exact hne ((derivative_eq_zero).mp h0)
    have := natDegree_le_of_dvd hdvd hdq
    have := natDegree_derivative_lt hne
    omega
  have hdq : derivative q = 0 := (derivative_eq_zero).mpr hq0
  have hdp : derivative p = 0 := by
    rw [hdq, mul_zero, sub_zero] at hnum
    exact (mul_eq_zero.mp hnum).resolve_left hq
  have hp0 : p.natDegree = 0 := (derivative_eq_zero).mp hdp
  obtain ⟨cp, hcp⟩ : ∃ c, p = C c := ⟨_, eq_C_of_natDegree_eq_zero hp0⟩
  obtain ⟨cq, hcq⟩ : ∃ c, q = C c := ⟨_, eq_C_of_natDegree_eq_zero hq0⟩
  refine ⟨cp / cq, ?_⟩
  rw [hfpq, hcp, hcq, ← algebraMap_C, ← algebraMap_C, map_div₀]

private theorem derivX_ne_zero_of_ord_ne_zero {v : Place ℂ (RatFunc ℂ)} {f : RatFunc ℂ}
    (h : v.ord f ≠ 0) :
    derivX f ≠ 0 := by
  intro h0
  obtain ⟨c, rfl⟩ := eq_algebraMap_of_derivX_eq_zero h0
  exact h (v.ord_algebraMap c)

private theorem span_D_X :
    Submodule.span (RatFunc ℂ) {KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X} = ⊤ :=
  KaehlerDifferential.span_D_eq_top_of_transcendental ℂ _ RatFunc.transcendental_X

private theorem dCoordGenerates (v : Place ℂ (RatFunc ℂ)) : v.DCoordGenerates := by
  refine ⟨?_⟩
  have hne : derivX v.uniformizer ≠ 0 :=
    derivX_ne_zero_of_ord_ne_zero (v := v) (by rw [v.ord_uniformizer]; exact one_ne_zero)
  rw [Place.dCoord, D_eq_derivX_smul, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hne), span_D_X]

attribute [local instance] dCoordGenerates

/-! ### The Riemann sphere structure on the places -/

@[instance_reducible]
private noncomputable def decEqPlace : DecidableEq (Place ℂ (RatFunc ℂ)) := Classical.decEq _

attribute [local instance] decEqPlace

private theorem pt_inj {a b : ℂ} : pt a = pt b ↔ a = b := (placeOfPoint_injective ℂ).eq_iff

private noncomputable def affineChart : PartialEquiv (Place ℂ (RatFunc ℂ)) ℂ where
  toFun v := (placeEquivOption ℂ v).getD 0
  invFun z := pt z
  source := {v | v ≠ ∞ₚ}
  target := Set.univ
  map_source' := fun _ _ => Set.mem_univ _
  map_target' := fun z _ => pt_ne_inf z
  left_inv' := fun v hv => by
    rcases eq_placeOfPoint_or_eq_placeInfty ℂ v with ⟨a, rfl⟩ | rfl
    · simp [placeEquivOption_placeOfPoint]
    · exact absurd rfl hv
  right_inv' := fun z _ => by simp [placeEquivOption_placeOfPoint]

private noncomputable def infChart : PartialEquiv (Place ℂ (RatFunc ℂ)) ℂ where
  toFun v := (placeEquivOption ℂ v).elim 0 (·⁻¹)
  invFun z := if z = 0 then ∞ₚ else pt z⁻¹
  source := {v | v ≠ pt 0}
  target := Set.univ
  map_source' := fun _ _ => Set.mem_univ _
  map_target' := fun z _ => by
    by_cases hz : z = 0
    · simp only [hz, ite_true]
      exact (pt_ne_inf 0).symm
    · simp only [hz, ite_false]
      intro h
      exact inv_ne_zero hz (pt_inj.mp h)
  left_inv' := fun v hv => by
    rcases eq_placeOfPoint_or_eq_placeInfty ℂ v with ⟨a, rfl⟩ | rfl
    · have ha : a ≠ 0 := fun h => hv (by rw [h])
      simp [placeEquivOption_placeOfPoint, ha]
    · simp [placeEquivOption_placeInfty]
  right_inv' := fun z _ => by
    by_cases hz : z = 0
    · simp [hz, placeEquivOption_placeInfty]
    · simp [hz, placeEquivOption_placeOfPoint]

private theorem affineChart_pt (z : ℂ) : affineChart (pt z) = z := by
  simp [affineChart, placeEquivOption_placeOfPoint]

private theorem affineChart_symm (z : ℂ) : affineChart.symm z = pt z := rfl

private theorem infChart_pt (z : ℂ) : infChart (pt z) = z⁻¹ := by
  simp [infChart, placeEquivOption_placeOfPoint]

private theorem infChart_inf : infChart ∞ₚ = 0 := by
  simp [infChart, placeEquivOption_placeInfty]

private theorem infChart_symm (z : ℂ) : infChart.symm z = if z = 0 then ∞ₚ else pt z⁻¹ := rfl

private theorem affineChart_infChart_symm (z : ℂ) : affineChart (infChart.symm z) = z⁻¹ := by
  by_cases hz : z = 0
  · simp [infChart_symm, hz, affineChart, placeEquivOption_placeInfty]
  · simp [infChart_symm, hz, affineChart_pt]

private theorem infChart_infChart_symm (z : ℂ) : infChart (infChart.symm z) = z :=
  infChart.right_inv (Set.mem_univ z)

private theorem affineChart_affineChart_symm (z : ℂ) : affineChart (affineChart.symm z) = z :=
  affineChart.right_inv (Set.mem_univ z)

private theorem infChart_affineChart_symm (z : ℂ) : infChart (affineChart.symm z) = z⁻¹ :=
  infChart_pt z

private theorem trans_source_affineChart_affineChart :
    (affineChart.symm.trans affineChart).source = Set.univ := by
  ext z
  simp [PartialEquiv.trans_source, affineChart, pt_ne_inf]

private theorem trans_source_affineChart_infChart :
    (affineChart.symm.trans infChart).source = {z | z ≠ 0} := by
  ext z
  simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_ofPred_eq]
  change z ∈ Set.univ ∧ pt z ≠ pt 0 ↔ z ≠ 0
  simp [pt_inj]

private theorem trans_source_infChart_affineChart :
    (infChart.symm.trans affineChart).source = {z | z ≠ 0} := by
  ext z
  simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_ofPred_eq]
  change z ∈ Set.univ ∧ (if z = 0 then ∞ₚ else pt z⁻¹) ≠ ∞ₚ ↔ z ≠ 0
  by_cases hz : z = 0 <;> simp [hz, pt_ne_inf]

private theorem trans_source_infChart_infChart :
    (infChart.symm.trans infChart).source = Set.univ := by
  ext z
  simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_univ, iff_true]
  exact ⟨Set.mem_univ z, infChart.map_target (Set.mem_univ z)⟩

private noncomputable def atlasCore : ChartedSpaceCore ℂ (Place ℂ (RatFunc ℂ)) where
  atlas := {affineChart, infChart}
  chartAt v := if v = ∞ₚ then infChart else affineChart
  mem_chart_source v := by
    by_cases hv : v = ∞ₚ
    · rw [ite_eq_left hv, hv]
      exact (pt_ne_inf 0).symm
    · rw [ite_eq_right hv]
      exact hv
  chart_mem_atlas v := by
    by_cases hv : v = ∞ₚ <;> simp [hv]
  open_source e e' he he' := by
    rcases he with rfl | rfl <;> rcases he' with rfl | rfl
    · rw [trans_source_affineChart_affineChart]; exact isOpen_univ
    · rw [trans_source_affineChart_infChart]; exact isOpen_ne
    · rw [trans_source_infChart_affineChart]; exact isOpen_ne
    · rw [trans_source_infChart_infChart]; exact isOpen_univ
  continuousOn_toFun e e' he he' := by
    rcases he with rfl | rfl <;> rcases he' with rfl | rfl
    · exact continuousOn_id.congr fun z _ => affineChart_affineChart_symm z
    · rw [trans_source_affineChart_infChart]
      exact continuousOn_inv₀.congr fun z _ => infChart_affineChart_symm z
    · rw [trans_source_infChart_affineChart]
      exact continuousOn_inv₀.congr fun z _ => affineChart_infChart_symm z
    · exact continuousOn_id.congr fun z _ => infChart_infChart_symm z

@[instance_reducible]
private noncomputable def topPlaces : TopologicalSpace (Place ℂ (RatFunc ℂ)) :=
  atlasCore.toTopologicalSpace

attribute [local instance] topPlaces

@[instance_reducible]
private noncomputable def chartedPlaces : ChartedSpace ℂ (Place ℂ (RatFunc ℂ)) :=
  atlasCore.toChartedSpace

attribute [local instance] chartedPlaces

private theorem extChartAt_symm_pt (a z : ℂ) : (extChartAt 𝓘(ℂ, ℂ) (pt a)).symm z = pt z := by
  rw [extChartAt_coe_symm]
  change (if pt a = ∞ₚ then infChart else affineChart).symm z = pt z
  rw [ite_eq_right (pt_ne_inf a)]
  rfl

private theorem extChartAt_pt (a : ℂ) (w : Place ℂ (RatFunc ℂ)) :
    extChartAt 𝓘(ℂ, ℂ) (pt a) w = affineChart w := by
  rw [extChartAt_coe]
  change (if pt a = ∞ₚ then infChart else affineChart) w = affineChart w
  rw [ite_eq_right (pt_ne_inf a)]

private theorem extChartAt_symm_inf (z : ℂ) :
    (extChartAt 𝓘(ℂ, ℂ) ∞ₚ).symm z = if z = 0 then ∞ₚ else pt z⁻¹ := by
  rw [extChartAt_coe_symm]
  change (if (∞ₚ : Place ℂ (RatFunc ℂ)) = ∞ₚ then infChart else affineChart).symm z = _
  rw [ite_eq_left rfl]
  rfl

private theorem extChartAt_inf (w : Place ℂ (RatFunc ℂ)) :
    extChartAt 𝓘(ℂ, ℂ) ∞ₚ w = infChart w := by
  rw [extChartAt_coe]
  change (if (∞ₚ : Place ℂ (RatFunc ℂ)) = ∞ₚ then infChart else affineChart) w = infChart w
  rw [ite_eq_left rfl]

/-! ### Readings of rational functions -/

private theorem eventuallyEq_of_eqOn {g : ℂ → ℂ} {P Q : ℂ[X]} {z₀ : ℂ} (hQ : Q.eval z₀ ≠ 0)
    (h : ∀ z, Q.eval z ≠ 0 → g z = P.eval z / Q.eval z) :
    g =ᶠ[𝓝 z₀] fun z => P.eval z / Q.eval z := by
  have hU : IsOpen {z : ℂ | Q.eval z ≠ 0} :=
    isOpen_ne_fun (Polynomial.continuous Q) continuous_const
  filter_upwards [hU.mem_nhds hQ] with z hz using h z hz

private theorem eventually_differentiableAt_of_eqOn {g : ℂ → ℂ} {P Q : ℂ[X]} {z₀ : ℂ}
    (hQ : Q.eval z₀ ≠ 0) (h : ∀ z, Q.eval z ≠ 0 → g z = P.eval z / Q.eval z) :
    ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ g z := by
  have hU : IsOpen {z : ℂ | Q.eval z ≠ 0} :=
    isOpen_ne_fun (Polynomial.continuous Q) continuous_const
  filter_upwards [hU.mem_nhds hQ] with z hz
  exact ((P.differentiableAt).div (Q.differentiableAt) hz).congr_of_eventuallyEq
    (eventuallyEq_of_eqOn hz h)

private theorem hasDerivAt_of_eqOn {g : ℂ → ℂ} {P Q : ℂ[X]} {z₀ : ℂ} (hQ : Q.eval z₀ ≠ 0)
    (h : ∀ z, Q.eval z ≠ 0 → g z = P.eval z / Q.eval z) :
    HasDerivAt g ((((derivative P).eval z₀ * Q.eval z₀ - P.eval z₀ * (derivative Q).eval z₀))
      / Q.eval z₀ ^ 2) z₀ :=
  ((P.hasDerivAt z₀).div (Q.hasDerivAt z₀) hQ).congr_of_eventuallyEq (eventuallyEq_of_eqOn hQ h)

/-! ### Finite places -/

private theorem isRational_pt (a : ℂ) : (pt a).IsRational := (pt a).isRational_of_isCurveOver

private theorem evalAt_pt_div (a : ℂ) {p q : ℂ[X]} (hq : q.eval a ≠ 0) (hv : (pt a).IsRational) :
    (pt a).evalAt hv (rf p / rf q) = p.eval a / q.eval a :=
  evalAt_eq_of_hasValueAt hv (hasValueAt_pt_div a hq)

private theorem denom_eval_ne_zero_of_mem (a : ℂ) {f : RatFunc ℂ}
    (hf : f ∈ (pt a).toValuationSubring) :
    f.denom.eval a ≠ 0 := by
  intro hd
  have hfv := (pt a).hasValueAt_evalAt (isRational_pt a) hf
  have hden : (pt a).HasValueAt (rf f.denom) 0 := by
    simpa [hd] using hasValueAt_pt_rf a f.denom
  have hmul := (pt a).hasValueAt_mul hfv hden
  have hfd : f * rf f.denom = rf f.num :=
    (eq_div_iff (RatFunc.algebraMap_ne_zero f.denom_ne_zero)).mp f.num_div_denom.symm
  rw [hfd, mul_zero] at hmul
  have hn : f.num.eval a = 0 := ((pt a).hasValueAt_unique (hasValueAt_pt_rf a f.num) hmul)
  exact not_isUnit_X_sub_C a (f.isCoprime_num_denom.isUnit_of_dvd' (dvd_iff_isRoot.mpr hn)
    (dvd_iff_isRoot.mpr hd))

private theorem evalAt_congr_place {v w : Place ℂ (RatFunc ℂ)} (h : v = w) (hv : v.IsRational)
    (hw : w.IsRational) (f : RatFunc ℂ) : v.evalAt hv f = w.evalAt hw f := by
  subst h
  rfl

private theorem chartRead_pt (a : ℂ) (f : RatFunc ℂ) (z : ℂ) :
    (pt a).chartRead f z = (pt z).evalAt (isRational_pt z) f := by
  rw [Place.chartRead_apply]
  exact evalAt_congr_place (extChartAt_symm_pt a z) _ _ f

private theorem chartRead_pt_eq (a : ℂ) (f : RatFunc ℂ) (z : ℂ) (hz : f.denom.eval z ≠ 0) :
    (pt a).chartRead f z = f.num.eval z / f.denom.eval z := by
  rw [chartRead_pt, ← evalAt_pt_div z hz (isRational_pt z), f.num_div_denom]

/-! ### The place at infinity -/

private theorem intDegree_rf_div {r q : ℂ[X]} (hr : r ≠ 0) (hq : q ≠ 0) :
    (rf r / rf q).intDegree = (r.natDegree : ℤ) - q.natDegree := by
  rw [div_eq_mul_inv, RatFunc.intDegree_mul (RatFunc.algebraMap_ne_zero hr)
    (inv_ne_zero (RatFunc.algebraMap_ne_zero hq)), RatFunc.intDegree_inv,
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, sub_eq_add_neg]

private theorem mem_inf_iff {f : RatFunc ℂ} (hf : f ≠ 0) :
    f ∈ (∞ₚ).toValuationSubring ↔ f.num.natDegree ≤ f.denom.natDegree := by
  rw [(∞ₚ).mem_iff_ord_nonneg hf, ord_placeInfty hf, RatFunc.intDegree]
  omega

private theorem hasValueAt_inf_div {p q : ℂ[X]} (hq : q ≠ 0) (hpq : p.natDegree ≤ q.natDegree) :
    (∞ₚ).HasValueAt (rf p / rf q) (p.coeff q.natDegree / q.leadingCoeff) := by
  set c := p.coeff q.natDegree / q.leadingCoeff with hc
  set r := p - C c * q with hr
  have hlc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
  have hrq : rf p / rf q - algebraMap ℂ (RatFunc ℂ) c = rf r / rf q := by
    rw [algebraMap_C, hr, map_sub, map_mul, sub_div, mul_div_assoc,
      div_self (RatFunc.algebraMap_ne_zero hq), mul_one]
  change rf p / rf q - algebraMap ℂ (RatFunc ℂ) c ∈ (∞ₚ).toValuationSubring.nonunits
  rw [hrq, ValuationSubring.mem_nonunits_iff_or]
  by_cases hr0 : r = 0
  · left
    rw [hr0, map_zero, zero_div]
  · right
    have hcoeff : r.coeff q.natDegree = 0 := by
      rw [hr, coeff_sub, coeff_C_mul, hc, ← leadingCoeff, div_mul_cancel₀ _ hlc, sub_self]
    have hrdeg : r.natDegree ≤ q.natDegree :=
      (natDegree_sub_le _ _).trans (max_le hpq ((natDegree_C_mul_le _ _).trans le_rfl))
    have hrlt : r.natDegree < q.natDegree := by
      refine lt_of_le_of_ne hrdeg fun h => hr0 ?_
      rw [← leadingCoeff_eq_zero, leadingCoeff, h, hcoeff]
    have hne : (rf r / rf q)⁻¹ ≠ 0 :=
      inv_ne_zero (div_ne_zero (RatFunc.algebraMap_ne_zero hr0) (RatFunc.algebraMap_ne_zero hq))
    rw [(∞ₚ).mem_iff_ord_nonneg hne, ord_placeInfty hne, RatFunc.intDegree_inv,
      intDegree_rf_div hr0 hq]
    omega

private theorem isRational_inf : (∞ₚ).IsRational := (∞ₚ).isRational_of_isCurveOver

private theorem chartRead_inf_zero (f : RatFunc ℂ) :
    (∞ₚ).chartRead f 0 = (∞ₚ).evalAt isRational_inf f := by
  rw [Place.chartRead_apply]
  exact evalAt_congr_place (by rw [extChartAt_symm_inf, ite_eq_left rfl]) _ _ f

private theorem chartRead_inf_ne (f : RatFunc ℂ) {z : ℂ} (hz : z ≠ 0) :
    (∞ₚ).chartRead f z = (pt z⁻¹).evalAt (isRational_pt z⁻¹) f := by
  rw [Place.chartRead_apply]
  exact evalAt_congr_place (by rw [extChartAt_symm_inf, ite_eq_right hz]) _ _ f

private theorem reflect_eval_inv {n : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ n) {z : ℂ} (hz : z ≠ 0) :
    p.eval z⁻¹ = (reflect n p).eval z * z⁻¹ ^ n := by
  let : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz)
  have h := eval₂_reflect_mul_pow (RingHom.id ℂ) z⁻¹ n p hp
  rw [invOf_eq_inv, inv_inv] at h
  simpa [eval₂_id] using h.symm

private theorem chartRead_inf_eq {f : RatFunc ℂ} (hf : f ∈ (∞ₚ).toValuationSubring) (z : ℂ)
    (hz : (reflect f.denom.natDegree f.denom).eval z ≠ 0) :
    (∞ₚ).chartRead f z = (reflect f.denom.natDegree f.num).eval z
      / (reflect f.denom.natDegree f.denom).eval z := by
  have hdeg : f.num.natDegree ≤ f.denom.natDegree := by
    by_cases hf0 : f = 0
    · simp [hf0]
    · exact (mem_inf_iff hf0).mp hf
  by_cases hz0 : z = 0
  · subst hz0
    have key : (∞ₚ).HasValueAt f (f.num.coeff f.denom.natDegree / f.denom.leadingCoeff) := by
      have h := hasValueAt_inf_div f.denom_ne_zero hdeg
      rwa [f.num_div_denom] at h
    rw [chartRead_inf_zero, evalAt_eq_of_hasValueAt _ key, ← coeff_zero_eq_eval_zero,
      ← coeff_zero_eq_eval_zero, coeff_reflect, coeff_reflect, revAt_le (Nat.zero_le _),
      Nat.sub_zero, leadingCoeff]
  · have hq : f.denom.eval z⁻¹ ≠ 0 := by
      rw [reflect_eval_inv le_rfl hz0]
      exact mul_ne_zero hz (pow_ne_zero _ (inv_ne_zero hz0))
    have key := evalAt_pt_div z⁻¹ hq (isRational_pt z⁻¹) (p := f.num)
    rw [f.num_div_denom] at key
    rw [chartRead_inf_ne f hz0, key, reflect_eval_inv hdeg hz0, reflect_eval_inv le_rfl hz0,
      mul_div_mul_right _ _ (pow_ne_zero _ (inv_ne_zero hz0))]

/-! ### The preferred charts are holomorphic coordinates -/

private theorem centre_pt (a : ℂ) : extChartAt 𝓘(ℂ, ℂ) (pt a) (pt a) = a := by
  rw [extChartAt_pt, affineChart_pt]

private theorem centre_inf : extChartAt 𝓘(ℂ, ℂ) ∞ₚ ∞ₚ = 0 := by
  rw [extChartAt_inf, infChart_inf]

private theorem reflect_denom_eval_zero (f : RatFunc ℂ) :
    (reflect f.denom.natDegree f.denom).eval 0 ≠ 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero]
  exact leadingCoeff_ne_zero.mpr f.denom_ne_zero

private theorem mem_nonunits_of_ord_pos {v : Place ℂ (RatFunc ℂ)} {f : RatFunc ℂ} (hf : f ≠ 0)
    (h : 0 < v.ord f) : f ∈ v.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or]
  right
  rw [v.mem_iff_ord_nonneg (inv_ne_zero hf), v.ord_inv]
  omega

private theorem uniformizer_pt_facts (a : ℂ) :
    (pt a).uniformizer.denom.eval a ≠ 0 ∧ (pt a).uniformizer.num.eval a = 0 ∧
      (derivative (pt a).uniformizer.num).eval a ≠ 0 := by
  set π := (pt a).uniformizer with hπ
  have hπ0 : π ≠ 0 := (pt a).uniformizer_ne_zero
  have hord : (pt a).ord π = 1 := (pt a).ord_uniformizer
  have hmem : π ∈ (pt a).toValuationSubring :=
    (pt a).mem_of_ord_nonneg hπ0 (by rw [hord]; exact zero_le_one)
  have hq := denom_eval_ne_zero_of_mem a hmem
  have h0 : (pt a).HasValueAt π 0 := by
    change π - algebraMap ℂ (RatFunc ℂ) 0 ∈ _
    rw [map_zero, sub_zero]
    exact mem_nonunits_of_ord_pos hπ0 (by rw [hord]; exact one_pos)
  have hval : (pt a).HasValueAt π (π.num.eval a / π.denom.eval a) := by
    have h := hasValueAt_pt_div a hq (p := π.num)
    rwa [π.num_div_denom] at h
  have hp : π.num.eval a = 0 := by
    have := (pt a).hasValueAt_unique hval h0
    rwa [div_eq_zero_iff, or_iff_left hq] at this
  refine ⟨hq, hp, fun hd => ?_⟩
  set p := π.num with hpdef
  have hp0 : p ≠ 0 := fun h => hπ0 (RatFunc.num_eq_zero_iff.mp h)
  obtain ⟨r, hr⟩ : (X - C a) ∣ p := dvd_iff_isRoot.mpr hp
  have hra : r.eval a = 0 := by
    have hdp : derivative p = r + (X - C a) * derivative r := by
      rw [hr, derivative_mul, derivative_X_sub_C, one_mul]
    rw [hdp] at hd
    simpa using hd
  obtain ⟨t, ht⟩ : (X - C a) ∣ r := dvd_iff_isRoot.mpr hra
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ht
    rw [ht, mul_zero] at hr
    exact hp0 hr
  have hdecomp : π = rf (X - C a) * rf (X - C a) * (rf t / rf π.denom) := by
    conv_lhs => rw [← π.num_div_denom]
    rw [← hpdef, hr, ht, map_mul, map_mul]
    ring
  have hlin : rf (X - C a) ≠ 0 := RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a)
  have hrest : rf t / rf π.denom ≠ 0 :=
    div_ne_zero (RatFunc.algebraMap_ne_zero ht0) (RatFunc.algebraMap_ne_zero π.denom_ne_zero)
  have hrest_mem : rf t / rf π.denom ∈ (pt a).toValuationSubring :=
    (pt a).mem_of_hasValueAt (hasValueAt_pt_div a hq)
  have h2 := (pt a).ord_nonneg_of_mem hrest_mem
  rw [hdecomp, (pt a).ord_mul (mul_ne_zero hlin hlin) hrest, (pt a).ord_mul hlin hlin,
    ord_pt_X_sub_C, ite_eq_left rfl] at hord
  omega

private theorem uniformizer_inf_natDegree :
    (∞ₚ).uniformizer.num.natDegree + 1 = (∞ₚ).uniformizer.denom.natDegree := by
  have h := (∞ₚ).ord_uniformizer
  rw [ord_placeInfty (∞ₚ).uniformizer_ne_zero, RatFunc.intDegree] at h
  omega

private theorem isHolomorphicAtlas : IsHolomorphicAtlas (RatFunc ℂ) where
  eventually_differentiableAt_chartRead := by
    intro v f hf
    rcases eq_placeOfPoint_or_eq_placeInfty ℂ v with ⟨a, rfl⟩ | rfl
    · rw [centre_pt]
      exact eventually_differentiableAt_of_eqOn (denom_eval_ne_zero_of_mem a hf)
        (chartRead_pt_eq a f)
    · rw [centre_inf]
      exact eventually_differentiableAt_of_eqOn (reflect_denom_eval_zero f) (chartRead_inf_eq hf)
  deriv_chartRead_uniformizer_ne_zero := by
    intro v
    rcases eq_placeOfPoint_or_eq_placeInfty ℂ v with ⟨a, rfl⟩ | rfl
    · obtain ⟨hq, hp, hd⟩ := uniformizer_pt_facts a
      rw [centre_pt, (hasDerivAt_of_eqOn hq (chartRead_pt_eq a _)).deriv, hp, zero_mul, sub_zero]
      exact div_ne_zero (mul_ne_zero hd hq) (pow_ne_zero 2 hq)
    · have hπ0 : (∞ₚ).uniformizer ≠ 0 := (∞ₚ).uniformizer_ne_zero
      have hdeg := uniformizer_inf_natDegree
      set π := (∞ₚ).uniformizer with hπ
      set n := π.denom.natDegree with hn
      have hmem : π ∈ (∞ₚ).toValuationSubring := (mem_inf_iff hπ0).mpr (by omega)
      have hQ := reflect_denom_eval_zero π
      have hP0 : (reflect n π.num).eval 0 = 0 := by
        rw [← coeff_zero_eq_eval_zero, coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero]
        exact coeff_eq_zero_of_natDegree_lt (by omega)
      have hP1 : (derivative (reflect n π.num)).eval 0 ≠ 0 := by
        rw [← coeff_zero_eq_eval_zero, coeff_derivative, coeff_reflect, revAt_le (by omega)]
        have hnum0 : π.num ≠ 0 := fun h => hπ0 (RatFunc.num_eq_zero_iff.mp h)
        have : n - (0 + 1) = π.num.natDegree := by omega
        rw [this, ← leadingCoeff]
        simpa using leadingCoeff_ne_zero.mpr hnum0
      rw [centre_inf, (hasDerivAt_of_eqOn hQ (chartRead_inf_eq hmem)).deriv, hP0, zero_mul,
        sub_zero]
      exact div_ne_zero (mul_ne_zero hP1 hQ) (pow_ne_zero 2 hQ)

attribute [local instance] isHolomorphicAtlas

/-! ### The integral of `dX` from `0` to `1` -/

private theorem chartAt_pt (a : ℂ) :
    chartAt ℂ (pt a) = atlasCore.openPartialHomeomorph affineChart (Set.mem_insert _ _) := by
  change atlasCore.openPartialHomeomorph (atlasCore.chartAt (pt a))
    (atlasCore.chart_mem_atlas (pt a)) = _
  have h : atlasCore.chartAt (pt a) = affineChart := ite_eq_right (pt_ne_inf a)
  congr 1

private theorem chartAt_target (v : Place ℂ (RatFunc ℂ)) : (chartAt ℂ v).target = Set.univ := by
  change (if v = ∞ₚ then infChart else affineChart).target = Set.univ
  split_ifs <;> rfl

private theorem continuous_pt : Continuous fun z : ℂ => pt z := by
  have h : ContinuousOn (extChartAt 𝓘(ℂ, ℂ) (pt 0)).symm (extChartAt 𝓘(ℂ, ℂ) (pt 0)).target :=
    continuousOn_extChartAt_symm (pt 0)
  rw [extChartAt_target, chartAt_target] at h
  simp only [Set.preimage_univ, ModelWithCorners.range_eq_univ, Set.inter_self] at h
  rw [continuousOn_univ] at h
  convert h using 1
  funext z
  rw [extChartAt_symm_pt]

/-- The segment from the place `0` to the place `1`, in the affine coordinate. -/
private noncomputable def segment01 : Path (pt 0) (pt 1) where
  toFun t := pt ((t : ℝ) : ℂ)
  continuous_toFun := continuous_pt.comp (Complex.continuous_ofReal.comp continuous_subtype_val)
  source' := by simp
  target' := by simp

private theorem readDifferential_D_X_eventually (a : ℂ) :
    ∀ᶠ z in 𝓝 a, (pt a).readDifferential (KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X) z = 1 := by
  obtain ⟨hq, hp, hd⟩ := uniformizer_pt_facts a
  set π := (pt a).uniformizer with hπ
  set W := π.denom * derivative π.num - π.num * derivative π.denom with hW
  have hWa : W.eval a ≠ 0 := by
    simp only [hW, eval_sub, eval_mul, hp, zero_mul, sub_zero]
    exact mul_ne_zero hq hd
  have hderivX : derivX π = rf W / rf (π.denom ^ 2) := by
    conv_lhs => rw [← π.num_div_denom]
    rw [derivX_div]
  have hcoeff : (pt a).differentialCoeff (KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X)
      = rf (π.denom ^ 2) / rf W := by
    refine (pt a).differentialCoeff_unique ?_
    have hne : rf W * rf (π.denom ^ 2) ≠ 0 :=
      mul_ne_zero (RatFunc.algebraMap_ne_zero fun h => hWa (by rw [h, eval_zero]))
        (RatFunc.algebraMap_ne_zero (pow_ne_zero 2 π.denom_ne_zero))
    rw [Place.dCoord, D_eq_derivX_smul π, smul_smul, hderivX, div_mul_div_comm,
      mul_comm (rf (π.denom ^ 2)), div_self hne, one_smul]
  have hU : IsOpen {z : ℂ | π.denom.eval z ≠ 0 ∧ W.eval z ≠ 0} :=
    (isOpen_ne_fun (Polynomial.continuous _) continuous_const).inter
      (isOpen_ne_fun (Polynomial.continuous _) continuous_const)
  filter_upwards [hU.mem_nhds ⟨hq, hWa⟩] with z ⟨hqz, hWz⟩
  rw [Place.readDifferential_apply, hcoeff, ← hπ, chartRead_pt,
    evalAt_pt_div z hWz (isRational_pt z),
    (hasDerivAt_of_eqOn hqz (chartRead_pt_eq a π)).deriv]
  have hWz' : (derivative π.num).eval z * π.denom.eval z
      - π.num.eval z * (derivative π.denom).eval z = W.eval z := by
    simp only [hW, eval_sub, eval_mul]
    ring
  rw [hWz', eval_pow]
  field_simp

private theorem segment01_apply (t : unitInterval) : segment01 t = pt ((t : ℝ) : ℂ) := rfl

private theorem chartAt_segment01 (t : unitInterval) :
    chartAt ℂ (segment01 t) = chartAt ℂ (pt 0) := by
  rw [segment01_apply, chartAt_pt, chartAt_pt]

private theorem chartAt_pt_zero_apply (b : ℂ) : chartAt ℂ (pt 0) (pt b) = b := by
  rw [chartAt_pt]
  exact affineChart_pt b

private theorem hasDerivAt_id_readDifferential_D_X (t : unitInterval) :
    ∀ᶠ z in 𝓝 (chartAt ℂ (pt 0) (segment01 t)),
      HasDerivAt id
        ((segment01 t).readDifferential (KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X) z) z := by
  rw [segment01_apply, chartAt_pt_zero_apply]
  filter_upwards [readDifferential_D_X_eventually ((t : ℝ) : ℂ)] with z hz
  rw [hz]
  exact hasDerivAt_id z

private theorem isPrimitiveAlong_D_X :
    IsPrimitiveAlong (KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X) segment01
      fun t => id (chartAt ℂ (pt 0) (segment01 t)) :=
  isPrimitiveAlong_of_chartAt_eq chartAt_segment01 hasDerivAt_id_readDifferential_D_X

/-- **The integral of `dX` from `0` to `1`.** On the complex projective line, the line integral of
`dX` along the segment from the place `0` to the place `1` is `1`. -/
example (h : ∃ g, IsPrimitiveAlong (KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X) segment01 g) :
    pathIntegral (KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X) segment01 h = 1 := by
  rw [pathIntegral_eq_sub_of_chartAt_eq chartAt_segment01 hasDerivAt_id_readDifferential_D_X h,
    chartAt_pt_zero_apply, chartAt_pt_zero_apply]
  simp

example : ∃ g, IsPrimitiveAlong (KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X) segment01 g :=
  ⟨_, isPrimitiveAlong_D_X⟩

end

end AlgebraicCurve.ComplexLineIntegralTest
