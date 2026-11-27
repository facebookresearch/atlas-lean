/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Definitions/Def_AlgebraicCurve_TwoChartIntegralModel.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Localization.Integral
public import MathlibExt.AlgebraicGeometry.Curve.GluedCharts

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicCurve

namespace TwoChartIntegralModel

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

variable {F} in
public theorem j_ne_zero : j ≠ 0 := Fact.out

/-- The integral closure of `R[S]` in `F`, as an `R`-subalgebra of `F`: the chart ring at `S` of
the two-chart gluing. -/
public abbrev chartAlg (S : Set F) : Subalgebra R F :=
  (integralClosure (Algebra.adjoin R S) F).restrictScalars R

public theorem mem_chartAlg_iff {S : Set F} {x : F} :
    x ∈ chartAlg R F S ↔ IsIntegral (Algebra.adjoin R S) x :=
  (Subalgebra.mem_restrictScalars R).trans (mem_integralClosure_iff _ _)

public theorem adjoin_le_chartAlg (S : Set F) :
    Algebra.adjoin R S ≤ chartAlg R F S := fun x hx => by
  rw [mem_chartAlg_iff]
  exact isIntegral_algebraMap (x := (⟨x, hx⟩ : Algebra.adjoin R S))

public theorem subset_chartAlg (S : Set F) : S ⊆ (chartAlg R F S : Set F) := fun _ hx =>
  adjoin_le_chartAlg R F S (Algebra.subset_adjoin hx)

public theorem chartAlg_mono {S S' : Set F} (h : S ⊆ S') : chartAlg R F S ≤ chartAlg R F S' := by
  intro x hx
  rw [mem_chartAlg_iff] at hx ⊢
  exact hx.map_of_comp_eq
    (Subalgebra.inclusion (Algebra.adjoin_mono h)).toRingHom (RingHom.id F) (by ext; rfl)

public abbrev chartIncl {S S' : Set F} (h : S ⊆ S') : chartAlg R F S →ₐ[R] chartAlg R F S' :=
  Subalgebra.inclusion (chartAlg_mono R F h)

public theorem coe_chartIncl {S S' : Set F} (h : S ⊆ S') (x : chartAlg R F S) :
    (chartIncl R F h x : F) = x :=
  Subalgebra.coe_inclusion _ x

public theorem chartIncl_injective {S S' : Set F} (h : S ⊆ S') :
    Function.Injective (chartIncl R F h) :=
  Subalgebra.inclusion_injective _

variable {R F j}

public theorem exists_pow_mul_mem_adjoin {S : Set F} {s : F} (hs : s ∈ S) (hs0 : s ≠ 0) {x : F}
    (hx : x ∈ Algebra.adjoin R (insert s⁻¹ S)) : ∃ n : ℕ, s ^ n * x ∈ Algebra.adjoin R S := by
  have hsA : s ∈ Algebra.adjoin R S := Algebra.subset_adjoin hs
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact ⟨1, by rw [pow_one, mul_inv_cancel₀ hs0]; exact one_mem _⟩
    · exact ⟨0, by rw [pow_zero, one_mul]; exact Algebra.subset_adjoin hy⟩
  | algebraMap a => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ a⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : s ^ (m + n) * (y + z) = s ^ n * (s ^ m * y) + s ^ m * (s ^ n * z) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hsA n) hm) (mul_mem (pow_mem hsA m) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : s ^ (m + n) * (y * z) = (s ^ m * y) * (s ^ n * z) := by ring
    rw [this]
    exact mul_mem hm hn

public theorem isLocalization_away_adjoin {S T : Set F} {s : F} (hs : s ∈ S) (hs0 : s ≠ 0)
    (hST : S ⊆ T) (hsT : s⁻¹ ∈ T) (hTS : T ⊆ insert s⁻¹ S) :
    letI := (Subalgebra.inclusion (Algebra.adjoin_mono (R := R) hST)).toRingHom.toAlgebra
    IsLocalization.Away (⟨s, Algebra.subset_adjoin hs⟩ : Algebra.adjoin R S)
      (Algebra.adjoin R T) := by
  let := (Subalgebra.inclusion (Algebra.adjoin_mono (R := R) hST)).toRingHom.toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [RingHom.algebraMap_toAlgebra, map_pow]
    refine (IsUnit.of_mul_eq_one ⟨s⁻¹, Algebra.subset_adjoin hsT⟩ (Subtype.ext ?_)).pow n
    exact mul_inv_cancel₀ hs0
  · intro z
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_adjoin hs hs0 (Algebra.adjoin_mono hTS z.2)
    refine ⟨(⟨s ^ n * z, hn⟩, ⟨⟨s, Algebra.subset_adjoin hs⟩ ^ n, n, rfl⟩), Subtype.ext ?_⟩
    exact mul_comm _ _
  · intro x y h
    refine ⟨1, ?_⟩
    rw [RingHom.algebraMap_toAlgebra] at h
    rw [Subalgebra.inclusion_injective _ h]

public theorem isLocalization_away_chartIncl {S T : Set F} {s : F} (hs : s ∈ S) (hs0 : s ≠ 0)
    (hST : S ⊆ T) (hsT : s⁻¹ ∈ T) (hTS : T ⊆ insert s⁻¹ S) :
    letI := (chartIncl R F hST).toRingHom.toAlgebra
    IsLocalization.Away (⟨s, subset_chartAlg R F S hs⟩ : chartAlg R F S) (chartAlg R F T) := by
  let := (chartIncl R F hST).toRingHom.toAlgebra
  let := (Subalgebra.inclusion (Algebra.adjoin_mono (R := R) hST)).toRingHom.toAlgebra
  have : IsScalarTower (Algebra.adjoin R S) (Algebra.adjoin R T) F :=
    .of_algebraMap_eq fun _ => rfl
  have := isLocalization_away_adjoin (R := R) hs hs0 hST hsT hTS
  have : IsLocalization.Away
      (algebraMap (Algebra.adjoin R S) F ⟨s, Algebra.subset_adjoin hs⟩) F :=
    IsLocalization.away_of_isUnit_of_bijective F (IsUnit.mk0 _ hs0) Function.bijective_id
  let : Algebra (integralClosure (Algebra.adjoin R S) F) (integralClosure (Algebra.adjoin R T) F) :=
    (chartIncl R F hST).toRingHom.toAlgebra
  have : IsScalarTower (integralClosure (Algebra.adjoin R S) F)
      (integralClosure (Algebra.adjoin R T) F) F :=
    .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (Algebra.adjoin R S) (integralClosure (Algebra.adjoin R S) F)
      (integralClosure (Algebra.adjoin R T) F) :=
    .of_algebraMap_eq fun _ => rfl
  exact IsLocalization.Away.integralClosure (R := Algebra.adjoin R S) (S := F)
    (Rf := Algebra.adjoin R T) (Sf := F) ⟨s, Algebra.subset_adjoin hs⟩

variable (R F j)

omit [Fact (j ≠ 0)] in
public theorem sFin_subset : ({j} : Set F) ⊆ {j, j⁻¹} :=
  CurveModel.singleton_subset_pair j

omit [Fact (j ≠ 0)] in
public theorem sInf_subset : ({j⁻¹} : Set F) ⊆ {j, j⁻¹} :=
  CurveModel.singleton_inv_subset_pair j

public abbrev chartAlgFin : Subalgebra R F := chartAlg R F {j}

public abbrev chartAlgInf : Subalgebra R F := chartAlg R F {j⁻¹}

public abbrev chartAlgMid : Subalgebra R F := chartAlg R F {j, j⁻¹}

public def jChartFin : chartAlgFin R F j := ⟨j, subset_chartAlg R F _ rfl⟩

public def jInvChartInf : chartAlgInf R F j := ⟨j⁻¹, subset_chartAlg R F _ rfl⟩

omit [Fact (j ≠ 0)] in
@[simp] public theorem coe_jChartFin : (jChartFin R F j : F) = j := rfl
omit [Fact (j ≠ 0)] in
@[simp] public theorem coe_jInvChartInf : (jInvChartInf R F j : F) = j⁻¹ := rfl

public abbrev inclFin : chartAlgFin R F j →ₐ[R] chartAlgMid R F j := chartIncl R F (sFin_subset F j)

public abbrev inclInf : chartAlgInf R F j →ₐ[R] chartAlgMid R F j := chartIncl R F (sInf_subset F j)

public theorem isUnit_inclFin_jChartFin : IsUnit (inclFin R F j (jChartFin R F j)) := by
  refine .of_mul_eq_one ⟨j⁻¹, subset_chartAlg R F _ (by simp)⟩ (Subtype.ext ?_)
  rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_jChartFin]
  exact mul_inv_cancel₀ (j_ne_zero j)

public theorem isUnit_inclInf_jInvChartInf : IsUnit (inclInf R F j (jInvChartInf R F j)) := by
  refine .of_mul_eq_one ⟨j, subset_chartAlg R F _ (by simp)⟩ (Subtype.ext ?_)
  rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_jInvChartInf]
  exact inv_mul_cancel₀ (j_ne_zero j)

public theorem isLocalization_away_inclFin :
    letI := (inclFin R F j).toRingHom.toAlgebra
    IsLocalization.Away (jChartFin R F j) (chartAlgMid R F j) :=
  isLocalization_away_chartIncl (Set.mem_singleton j) (j_ne_zero j) (sFin_subset F j)
    (Set.mem_insert_of_mem _ rfl) (Set.pair_comm j j⁻¹).subset

public theorem isLocalization_away_inclInf :
    letI := (inclInf R F j).toRingHom.toAlgebra
    IsLocalization.Away (jInvChartInf R F j) (chartAlgMid R F j) :=
  isLocalization_away_chartIncl (Set.mem_singleton j⁻¹) (inv_ne_zero (j_ne_zero j))
    (sInf_subset F j) (by rw [inv_inv]; exact Set.mem_insert _ _) (by rw [inv_inv])

public abbrev XFin : Scheme.{u} := Spec (CommRingCat.of (chartAlgFin R F j))

public abbrev XInf : Scheme.{u} := Spec (CommRingCat.of (chartAlgInf R F j))

public abbrev XMid : Scheme.{u} := Spec (CommRingCat.of (chartAlgMid R F j))

public abbrev fFin : XMid R F j ⟶ XFin R F j :=
  Spec.map (CommRingCat.ofHom (inclFin R F j).toRingHom)

public abbrev fInf : XMid R F j ⟶ XInf R F j :=
  Spec.map (CommRingCat.ofHom (inclInf R F j).toRingHom)

instance isOpenImmersion_fFin : IsOpenImmersion (fFin R F j) := by
  let := (inclFin R F j).toRingHom.toAlgebra
  have := isLocalization_away_inclFin R F j
  exact IsOpenImmersion.of_isLocalization (jChartFin R F j)

instance isOpenImmersion_fInf : IsOpenImmersion (fInf R F j) := by
  let := (inclInf R F j).toRingHom.toAlgebra
  have := isLocalization_away_inclInf R F j
  exact IsOpenImmersion.of_isLocalization (jInvChartInf R F j)

/-- The scheme glued from chart rings inside `F` at `j ≠ 0`: `Spec` of the integral closures of
`R[j]` and `R[j⁻¹]` in `F`, glued along `Spec` of the integral closure of `R[j, j⁻¹]`, which is an
open subscheme of both. These hypotheses do not make its function field `F`: for `R = ℚ`,
`F = ℚ(t)` and `j = 1` all three chart rings are `ℚ`, so the glued scheme is `Spec ℚ`. Over a field
`K`, it is `AlgebraicCurve.CurveModel.glued K j` (`twoChartIntegralModel_eq_glued`), whose
function field is `F` when `F` is finite over `K(j)`
(`AlgebraicCurve.CurveModel.gluedFunctionFieldEquiv`). -/
public def _root_.AlgebraicCurve.TwoChartIntegralModel : Scheme.{u} :=
  pushout (fFin R F j) (fInf R F j)

public def ιFin : XFin R F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F j :=
  pushout.inl (fFin R F j) (fInf R F j)

public def ιInf : XInf R F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F j :=
  pushout.inr (fFin R F j) (fInf R F j)

public theorem glue_condition :
    fFin R F j ≫ ιFin R F j = fInf R F j ≫ ιInf R F j := pushout.condition

instance isOpenImmersion_ιFin : IsOpenImmersion (ιFin R F j) :=
  (Scheme.IsLocallyDirected.openCover (span (fFin R F j) (fInf R F j))).map_prop WalkingSpan.left

instance isOpenImmersion_ιInf : IsOpenImmersion (ιInf R F j) :=
  (Scheme.IsLocallyDirected.openCover (span (fFin R F j) (fInf R F j))).map_prop WalkingSpan.right

omit [Fact (j ≠ 0)] in
public theorem fFin_toBase_eq_fInf_toBase :
    fFin R F j ≫ Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgFin R F j))) =
      fInf R F j ≫ Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgInf R F j))) := by
  have h : (inclFin R F j).toRingHom.comp (algebraMap R (chartAlgFin R F j)) =
      (inclInf R F j).toRingHom.comp (algebraMap R (chartAlgInf R F j)) :=
    RingHom.ext fun a => ((inclFin R F j).commutes a).trans ((inclInf R F j).commutes a).symm
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

public def toBase : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ Spec (CommRingCat.of R) :=
  pushout.desc (Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgFin R F j))))
    (Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgInf R F j))))
    (fFin_toBase_eq_fInf_toBase R F j)

@[reassoc (attr := simp)]
public theorem ιFin_toBase : ιFin R F j ≫ toBase R F j =
    Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgFin R F j))) :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
public theorem ιInf_toBase : ιInf R F j ≫ toBase R F j =
    Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgInf R F j))) :=
  pushout.inr_desc _ _ _

public theorem mem_range_ιFin_or_mem_range_ιInf (x : AlgebraicCurve.TwoChartIntegralModel R F j) :
    x ∈ Set.range (ιFin R F j).base ∨ x ∈ Set.range (ιInf R F j).base := by
  obtain ⟨i, y, hy⟩ :=
    (Scheme.IsLocallyDirected.openCover (span (fFin R F j) (fInf R F j))).exists_eq x
  rcases i with (_ | _ | _)
  · have hw : (Scheme.IsLocallyDirected.openCover (span (fFin R F j) (fInf R F j))).f none =
        fFin R F j ≫ ιFin R F j :=
      (colimit.w (span (fFin R F j) (fInf R F j)) WalkingSpan.Hom.fst).symm
    refine Or.inl ⟨(fFin R F j).base y, ?_⟩
    rw [← hy, hw]; rfl
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

public def chartFinOpen : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens :=
  (ιFin R F j).opensRange

public def chartInfOpen : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens :=
  (ιInf R F j).opensRange

public theorem isAffineOpen_chartFinOpen : IsAffineOpen (chartFinOpen R F j) :=
  isAffineOpen_opensRange (ιFin R F j)

public theorem isAffineOpen_chartInfOpen : IsAffineOpen (chartInfOpen R F j) :=
  isAffineOpen_opensRange (ιInf R F j)

public theorem twoChartCover : chartFinOpen R F j ⊔ chartInfOpen R F j = ⊤ := by
  rw [chartFinOpen, chartInfOpen, ← TopologicalSpace.Opens.coe_inj]
  ext x
  simpa using mem_range_ιFin_or_mem_range_ιInf R F j x

public def polynomialToChartFin : Polynomial R →ₐ[R] chartAlgFin R F j :=
  Polynomial.aeval (jChartFin R F j)

public def polynomialToChartInf : Polynomial R →ₐ[R] chartAlgInf R F j :=
  Polynomial.aeval (jInvChartInf R F j)

omit [Fact (j ≠ 0)] in
@[simp] public theorem polynomialToChartFin_X :
    polynomialToChartFin R F j Polynomial.X = jChartFin R F j :=
  Polynomial.aeval_X _

omit [Fact (j ≠ 0)] in
@[simp] public theorem polynomialToChartInf_X :
    polynomialToChartInf R F j Polynomial.X = jInvChartInf R F j :=
  Polynomial.aeval_X _

public def baseChange (S : Type u) [CommRing S] [Algebra R S] : Scheme.{u} :=
  pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))

public def baseChangeι (S : Type u) [CommRing S] [Algebra R S] :
    baseChange R F j S ⟶ AlgebraicCurve.TwoChartIntegralModel R F j := pullback.fst _ _

public def baseChangeToBase (S : Type u) [CommRing S] [Algebra R S] :
    baseChange R F j S ⟶ Spec (CommRingCat.of S) := pullback.snd _ _

@[reassoc]
public theorem baseChangeι_toBase (S : Type u) [CommRing S] [Algebra R S] :
    baseChangeι R F j S ≫ toBase R F j =
      baseChangeToBase R F j S ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) :=
  pullback.condition

/-- The reduction of the glued scheme modulo an ideal `I` of `R`: its base change along the
quotient map `R → R ⧸ I`, which lies over the closed subscheme `V(I)` of `Spec R`. When `I` is
maximal, `R ⧸ I` is the residue field at the closed point `I` and this is the fibre over that
point; in general it is not a fibre over a point (for `I = ⊥` it is the whole glued scheme, up to
isomorphism). -/
public abbrev reduction (I : Ideal R) : Scheme.{u} := baseChange R F j (R ⧸ I)

public abbrev reductionι (I : Ideal R) :
    reduction R F j I ⟶ AlgebraicCurve.TwoChartIntegralModel R F j :=
  baseChangeι R F j (R ⧸ I)

public abbrev reductionToBase (I : Ideal R) : reduction R F j I ⟶ Spec (CommRingCat.of (R ⧸ I)) :=
  baseChangeToBase R F j (R ⧸ I)

@[reassoc]
public theorem reductionι_toBase (I : Ideal R) :
    reductionι R F j I ≫ toBase R F j =
      reductionToBase R F j I ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
  pullback.condition

section CoefficientExtension

variable (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]

public theorem adjoin_le_adjoin_restrictScalars (S : Set F) :
    Algebra.adjoin R S ≤ (Algebra.adjoin R' S).restrictScalars R :=
  Algebra.adjoin_le Algebra.subset_adjoin

public theorem chartAlg_le_chartAlg (S : Set F) :
    (chartAlg R F S).toSubring ≤ (chartAlg R' F S).toSubring := by
  intro x hx
  change IsIntegral (Algebra.adjoin R' S) x
  have hx' : IsIntegral (Algebra.adjoin R S) x := hx
  have hle : (Algebra.adjoin R S).toSubring ≤ ((Algebra.adjoin R' S).restrictScalars R).toSubring :=
    fun y hy => adjoin_le_adjoin_restrictScalars R F R' S hy
  exact hx'.map_of_comp_eq (Subring.inclusion hle) (RingHom.id F) (by ext; rfl)

public theorem chartAlg_le_restrictScalars (S : Set F) :
    chartAlg R F S ≤ (chartAlg R' F S).restrictScalars R :=
  fun _ hx => chartAlg_le_chartAlg R F R' S hx

/-- For a scalar tower `R → R' → F`, the inclusion of chart rings
`chartAlg R F S → chartAlg R' F S` inside `F` induced by extending the coefficient ring from `R`
to `R'`. It is not the scalar extension `R' ⊗[R] chartAlg R F S` in general: for `R = ℤ`,
`R' = ℤ[T]` acting on `ℚ` by `T ↦ 0` and `S = {2}`, both chart rings are `ℤ`, while the scalar
extension is `ℤ[T]`. The base change of the glued scheme along `Spec R' → Spec R` is the pullback
`baseChange`. -/
public def chartCoeffIncl (S : Set F) : chartAlg R F S →+* chartAlg R' F S :=
  (Subalgebra.inclusion (chartAlg_le_restrictScalars R F R' S)).toRingHom

@[simp] public theorem coe_chartCoeffIncl (S : Set F) (x : chartAlg R F S) :
    (chartCoeffIncl R F R' S x : F) = x :=
  Subalgebra.coe_inclusion _ x

public theorem chartCoeffIncl_algebraMap (S : Set F) (r : R) :
    chartCoeffIncl R F R' S (algebraMap R (chartAlg R F S) r) =
      algebraMap R' (chartAlg R' F S) (algebraMap R R' r) :=
  Subtype.ext (IsScalarTower.algebraMap_apply R R' F r)

end CoefficientExtension

section FieldCase

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]

public theorem chartAlg_eq_chartRing (S : Set L) : chartAlg K L S = CurveModel.chartRing K S :=
  rfl

variable (t : L) [Fact (t ≠ 0)]

public theorem twoChartIntegralModel_eq_glued :
    AlgebraicCurve.TwoChartIntegralModel K L t = CurveModel.glued K t :=
  rfl

public theorem ιFin_eq_ι₀ : ιFin K L t = CurveModel.ι₀ K t :=
  rfl

public theorem ιInf_eq_curveModel_ιInf : ιInf K L t = CurveModel.ιInf K t :=
  rfl

public theorem toBase_eq_gluedToBase : toBase K L t = CurveModel.gluedToBase K t :=
  rfl

end FieldCase

end TwoChartIntegralModel

end AlgebraicCurve

end
