/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_JacJ1_ChartAlgebra.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Valuation.Integral
public import MathlibExt.AlgebraicGeometry.Curve.DivisorClassGroup
public import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaces
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Chart rings of a one-variable function field

For a field extension `L / K` and a set `S ⊆ L`, `AlgebraicCurve.CurveModel.chartRing K S` is the
integral closure of `K[S]` in `L`. When `s` is an element with `L` finite and separable over
`K(s)`, the chart ring of `{s}` is a Dedekind domain of finite type over `K` with fraction field
`L`, and its height-one primes correspond to the places of `L / K` at which `s` is integral
(`AlgebraicCurve.CurveModel.primeEquivChartPlaces`).
-/

@[expose] public section

noncomputable section

open Polynomial IsDedekindDomain IntermediateField

universe u

namespace AlgebraicCurve

namespace CurveModel

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L]

/-- Evaluation of polynomials at `s`, with values in `K[s]`. -/
private def aevalAdjoin (s : L) : K[X] →ₐ[K] Algebra.adjoin K ({s} : Set L) :=
  (aeval (R := K) s).codRestrict (Algebra.adjoin K ({s} : Set L))
    (fun p => by simp [Algebra.adjoin_singleton_eq_range_aeval])

private theorem aevalAdjoin_surjective (s : L) : Function.Surjective (aevalAdjoin K s) := by
  rintro ⟨x, hx⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨p, rfl⟩ := hx
  exact ⟨p, rfl⟩

scoped instance isPrincipalIdealRing_adjoin_singleton (s : L) :
    IsPrincipalIdealRing (Algebra.adjoin K ({s} : Set L)) :=
  IsPrincipalIdealRing.of_surjective (aevalAdjoin K s).toRingHom (aevalAdjoin_surjective K s)

scoped instance isDedekindDomain_adjoin_singleton (s : L) :
    IsDedekindDomain (Algebra.adjoin K ({s} : Set L)) :=
  inferInstance

/-- The chart ring of `S`: the integral closure of `K[S]` in `L`. -/
abbrev chartRing (S : Set L) : Subalgebra K L :=
  (integralClosure (Algebra.adjoin K S) L).restrictScalars K

theorem mem_chartRing_iff {S : Set L} {x : L} :
    x ∈ chartRing K S ↔ IsIntegral (Algebra.adjoin K S) x := Iff.rfl

theorem adjoin_le_chartRing (S : Set L) : Algebra.adjoin K S ≤ chartRing K S := by
  intro x hx
  rw [mem_chartRing_iff]
  have : IsIntegral (Algebra.adjoin K S) (algebraMap (Algebra.adjoin K S) L ⟨x, hx⟩) :=
    isIntegral_algebraMap
  exact this

theorem subset_chartRing (S : Set L) : S ⊆ (chartRing K S : Set L) := fun _ hx =>
  adjoin_le_chartRing K S (Algebra.subset_adjoin hx)

theorem chartRing_mono {S S' : Set L} (h : S ⊆ S') : chartRing K S ≤ chartRing K S' := by
  intro x hx
  rw [mem_chartRing_iff] at hx ⊢
  have := hx.map_of_comp_eq (Subalgebra.inclusion (Algebra.adjoin_mono h)).toRingHom
    (RingHom.id L) (by ext a; rfl)
  simpa using this

/-- The inclusion of chart rings induced by an inclusion of generating sets. -/
abbrev chartIncl {S S' : Set L} (h : S ⊆ S') : chartRing K S →ₐ[K] chartRing K S' :=
  Subalgebra.inclusion (chartRing_mono K h)

theorem coe_chartIncl {S S' : Set L} (h : S ⊆ S') (x : chartRing K S) :
    (chartIncl K h x : L) = x :=
  Subalgebra.coe_inclusion _ x

theorem chartIncl_injective {S S' : Set L} (h : S ⊆ S') :
    Function.Injective (chartIncl K h) :=
  Subalgebra.inclusion_injective _

instance algebraAdjoin (S : Set L) : Algebra (Algebra.adjoin K S) (chartRing K S) :=
  (Subalgebra.inclusion (adjoin_le_chartRing K S)).toRingHom.toAlgebra

instance isScalarTower_adjoin (S : Set L) :
    IsScalarTower (Algebra.adjoin K S) (chartRing K S) L :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

instance isScalarTower_base_adjoin (S : Set L) :
    IsScalarTower K (Algebra.adjoin K S) (chartRing K S) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

instance isIntegralClosure (S : Set L) :
    IsIntegralClosure (chartRing K S) (Algebra.adjoin K S) L where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩

section OneGenerator

variable (s : L) [FiniteDimensional K⟮s⟯ L] [Algebra.IsSeparable K⟮s⟯ L]

open scoped IntermediateField.algebraAdjoinAdjoin in
instance isDedekindDomain_chartRing : IsDedekindDomain (chartRing K ({s} : Set L)) :=
  IsIntegralClosure.isDedekindDomain (Algebra.adjoin K ({s} : Set L)) K⟮s⟯ L _

open scoped IntermediateField.algebraAdjoinAdjoin in
instance finite_chartRing :
    Module.Finite (Algebra.adjoin K ({s} : Set L)) (chartRing K ({s} : Set L)) :=
  IsIntegralClosure.finite (Algebra.adjoin K ({s} : Set L)) K⟮s⟯ L _

open scoped IntermediateField.algebraAdjoinAdjoin in
instance isFractionRing_chartRing : IsFractionRing (chartRing K ({s} : Set L)) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension (Algebra.adjoin K ({s} : Set L)) K⟮s⟯ L _

instance finiteType_chartRing : Algebra.FiniteType K (chartRing K ({s} : Set L)) :=
  (Algebra.FiniteType.adjoin_of_finite (R := K) (Set.finite_singleton s)).trans
    (inferInstance :
      Algebra.FiniteType (Algebra.adjoin K ({s} : Set L)) (chartRing K ({s} : Set L)))

instance isNoetherianRing_chartRing : IsNoetherianRing (chartRing K ({s} : Set L)) :=
  inferInstance

end OneGenerator

section Valuation

variable {K}

theorem adjoin_le_valuationSubring (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) {S : Set L} (hS : S ⊆ O) {y : L}
    (hy : y ∈ Algebra.adjoin K S) : y ∈ O := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy => exact hS hy
  | algebraMap a => exact hK a
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

/-- A valuation subring containing the image of `K`, as a `K`-subalgebra. -/
private def _root_.ValuationSubring.toSubalgebraOfBase (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) : Subalgebra K L :=
  { O.toSubring with algebraMap_mem' := hK }

private theorem _root_.ValuationSubring.integers_toSubalgebraOfBase (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) : O.valuation.Integers (O.toSubalgebraOfBase hK) where
  hom_inj := Subtype.val_injective
  map_le_one a := (O.valuation_le_one_iff _).mpr a.2
  exists_of_le_one r hr := ⟨⟨r, O.mem_of_valuation_le_one r hr⟩, rfl⟩

theorem chartRing_le_valuationSubring (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) {S : Set L} (hS : S ⊆ O) {x : L}
    (hx : x ∈ chartRing K S) : x ∈ O := by
  have hle : Algebra.adjoin K S ≤ O.toSubalgebraOfBase hK :=
    fun y hy => adjoin_le_valuationSubring O hK hS hy
  have hxO : IsIntegral (O.toSubalgebraOfBase hK) x := by
    have := ((mem_chartRing_iff K).mp hx).map_of_comp_eq (Subalgebra.inclusion hle).toRingHom
      (RingHom.id L) (by ext a; rfl)
    simpa using this
  exact O.mem_of_valuation_le_one x
    ((O.integers_toSubalgebraOfBase hK).isIntegral_iff_v_le_one.mp hxO)

variable (K)
variable (s : L)

/-- The centre on the chart ring of `{s}` of a valuation subring containing `K` and `s`. -/
def centre (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O) (hs : s ∈ O) :
    Ideal (chartRing K ({s} : Set L)) where
  carrier := {a | O.valuation a < 1}
  add_mem' {a b} ha hb := lt_of_le_of_lt (O.valuation.map_add a b) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c a ha := by
    have hc : O.valuation c ≤ 1 := (O.valuation_le_one_iff _).mpr
      (chartRing_le_valuationSubring O hK (Set.singleton_subset_iff.mpr hs) c.2)
    change O.valuation ((c : L) * a) < 1
    rw [map_mul]
    exact mul_lt_of_le_one_of_lt hc ha

theorem mem_centre_iff (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O)
    (hs : s ∈ O) (a : chartRing K ({s} : Set L)) :
    a ∈ centre K s O hK hs ↔ O.valuation a < 1 := Iff.rfl

theorem valuation_coe_le_one (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O)
    (hs : s ∈ O) (a : chartRing K ({s} : Set L)) : O.valuation a ≤ 1 :=
  (O.valuation_le_one_iff _).mpr
    (chartRing_le_valuationSubring O hK (Set.singleton_subset_iff.mpr hs) a.2)

theorem valuation_eq_one_of_not_mem_centre (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) (hs : s ∈ O) {a : chartRing K ({s} : Set L)}
    (ha : a ∉ centre K s O hK hs) : O.valuation a = 1 :=
  le_antisymm (valuation_coe_le_one K s O hK hs a) (not_lt.mp ha)

instance centre_isPrime (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O)
    (hs : s ∈ O) : (centre K s O hK hs).IsPrime where
  ne_top' := by
    rw [Ne, Ideal.eq_top_iff_one, mem_centre_iff]
    simp
  mem_or_mem' {a b} hab := by
    by_contra h
    push Not at h
    rw [mem_centre_iff, Subalgebra.coe_mul, map_mul,
      valuation_eq_one_of_not_mem_centre K s O hK hs h.1,
      valuation_eq_one_of_not_mem_centre K s O hK hs h.2, mul_one] at hab
    exact lt_irrefl _ hab

/-- The places of `L / K` at which `s` is integral. -/
def chartPlaces (s : L) : Set (Place K L) := {v | s ∈ v.toValuationSubring}

theorem mem_chartPlaces_iff {s : L} {v : Place K L} :
    v ∈ chartPlaces K s ↔ s ∈ v.toValuationSubring := Iff.rfl

theorem mem_chartPlaces_or_mem_chartPlaces_inv (v : Place K L) (t : L) :
    v ∈ chartPlaces K t ∨ v ∈ chartPlaces K t⁻¹ :=
  v.toValuationSubring.mem_or_inv_mem t

variable [FiniteDimensional K⟮s⟯ L] [Algebra.IsSeparable K⟮s⟯ L]

omit [Algebra.IsSeparable K⟮s⟯ L] in
theorem centre_ne_bot (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O)
    (hs : s ∈ O) (hO : O ≠ ⊤) : centre K s O hK hs ≠ ⊥ := by
  intro hbot
  apply hO
  refine top_unique fun x _ => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := chartRing K ({s} : Set L)) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbc : b ∉ centre K s O hK hs := by rw [hbot]; simpa using hb0
  apply O.mem_of_valuation_le_one
  rw [map_div₀, show O.valuation (algebraMap _ L b) = 1 from
    valuation_eq_one_of_not_mem_centre K s O hK hs hbc, div_one]
  exact valuation_coe_le_one K s O hK hs a

/-- For `L` finite over `K(s)`, the height-one prime of the chart ring of `{s}` at which a
nontrivial valuation subring containing `K` and `s` is centred. -/
def primeOfValuationSubring (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O)
    (hs : s ∈ O) (hO : O ≠ ⊤) : HeightOneSpectrum (chartRing K ({s} : Set L)) :=
  ⟨centre K s O hK hs, inferInstance, centre_ne_bot K s O hK hs hO⟩

theorem valuationSubringAtPrime_le (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) (hs : s ∈ O) (hO : O ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime L (primeOfValuationSubring K s O hK hs hO) ≤ O := by
  intro x hx
  have hx' : ∃ (a b : chartRing K ({s} : Set L)) (_ : b ∈ (centre K s O hK hs).primeCompl),
      x = algebraMap _ L a * (algebraMap _ L b)⁻¹ := hx
  obtain ⟨a, b, hb, rfl⟩ := hx'
  apply O.mem_of_valuation_le_one
  rw [map_mul, map_inv₀, show O.valuation (algebraMap _ L b) = 1 from
    valuation_eq_one_of_not_mem_centre K s O hK hs hb, inv_one, mul_one]
  exact valuation_coe_le_one K s O hK hs a

theorem valuationSubringAtPrime_primeOfValuationSubring (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) (hs : s ∈ O) (hO : O ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime L (primeOfValuationSubring K s O hK hs hO) = O :=
  ValuationSubring.eq_of_le_of_ne_top _ (valuationSubringAtPrime_le K s O hK hs hO) hO

theorem exists_ofHeightOneSpectrum_eq (v : Place K L) (hs : s ∈ v.toValuationSubring) :
    ∃ 𝔭 : HeightOneSpectrum (chartRing K ({s} : Set L)),
      Place.ofHeightOneSpectrum (K := K) 𝔭 = v := by
  refine ⟨primeOfValuationSubring K s v.toValuationSubring v.algebraMap_mem' hs v.ne_top', ?_⟩
  apply Place.ext
  rw [Place.ofHeightOneSpectrum_toValuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact valuationSubringAtPrime_primeOfValuationSubring K s _ _ hs _

theorem mem_ofHeightOneSpectrum (𝔭 : HeightOneSpectrum (chartRing K ({s} : Set L))) :
    s ∈ (Place.ofHeightOneSpectrum (K := K) (F := L) 𝔭).toValuationSubring := by
  rw [Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff]
  exact 𝔭.valuation_le_one (K := L)
    (⟨s, subset_chartRing K ({s} : Set L) (Set.mem_singleton s)⟩ : chartRing K ({s} : Set L))

/-- When `L` is finite and separable over `K(s)`, the height-one primes of the chart ring of `{s}`
are the places of `L / K` at which `s` is integral. -/
def primeEquivChartPlaces : HeightOneSpectrum (chartRing K ({s} : Set L)) ≃ chartPlaces K s :=
  Equiv.ofBijective
    (fun 𝔭 => ⟨Place.ofHeightOneSpectrum (K := K) 𝔭, mem_ofHeightOneSpectrum K s 𝔭⟩)
    ⟨fun 𝔭 𝔮 h => Place.ofHeightOneSpectrum_injective (K := K) (congrArg Subtype.val h),
     fun v => by
      obtain ⟨𝔭, h𝔭⟩ := exists_ofHeightOneSpectrum_eq K s v.1 v.2
      exact ⟨𝔭, Subtype.ext h𝔭⟩⟩

@[simp] theorem coe_primeEquivChartPlaces (𝔭 : HeightOneSpectrum (chartRing K ({s} : Set L))) :
    (primeEquivChartPlaces K s 𝔭 : Place K L) = Place.ofHeightOneSpectrum (K := K) 𝔭 :=
  rfl

end Valuation

section InvertGenerator

variable {K}

theorem exists_pow_mul_mem_adjoin {S : Set L} {s : L} (hs : s ∈ S) (hs0 : s ≠ 0) {x : L}
    (hx : x ∈ Algebra.adjoin K (insert s⁻¹ S)) : ∃ n : ℕ, s ^ n * x ∈ Algebra.adjoin K S := by
  have hsA : s ∈ Algebra.adjoin K S := Algebra.subset_adjoin hs
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

theorem exists_pow_mul_mem_chartRing {S : Set L} {s : L} (hs : s ∈ S) (hs0 : s ≠ 0) {x : L}
    (hx : x ∈ chartRing K (insert s⁻¹ S)) : ∃ n : ℕ, s ^ n * x ∈ chartRing K S := by
  classical
  obtain ⟨p, hmonic, hroot⟩ := (mem_chartRing_iff K).mp hx
  have hcoeff : ∀ i, ∃ n : ℕ, s ^ n * (p.coeff i : L) ∈ Algebra.adjoin K S :=
    fun i => exists_pow_mul_mem_adjoin hs hs0 (p.coeff i).2
  choose n hn using hcoeff
  set N : ℕ := ∑ i ∈ Finset.range (p.natDegree + 1), n i with hN
  have hnN : ∀ i ≤ p.natDegree, n i ≤ N := fun i hi =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  set q : L[X] := (p.map (algebraMap (Algebra.adjoin K (insert s⁻¹ S)) L)).scaleRoots (s ^ N)
    with hq
  have hqmonic : q.Monic := (Polynomial.monic_scaleRoots_iff _).mpr (hmonic.map _)
  have hqroot : q.eval (s ^ N * x) = 0 := by
    rw [hq, Polynomial.scaleRoots_eval_mul, Polynomial.eval_map, hroot, mul_zero]
  have hqcoeff : ∀ i, q.coeff i ∈ Algebra.adjoin K S := by
    intro i
    rw [hq, Polynomial.coeff_scaleRoots, Polynomial.coeff_map, hmonic.natDegree_map]
    by_cases hi : i < p.natDegree
    · have hle : n i ≤ N * (p.natDegree - i) := by
        calc n i ≤ N := hnN i hi.le
          _ = N * 1 := (mul_one N).symm
          _ ≤ N * (p.natDegree - i) :=
            Nat.mul_le_mul_left N (Nat.one_le_iff_ne_zero.mpr (by omega))
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      have : (s ^ N) ^ (p.natDegree - i) = s ^ k * s ^ n i := by
        rw [← pow_mul, hk, pow_add, mul_comm]
      rw [this, Subalgebra.algebraMap_def, Algebra.algebraMap_self_apply,
        show (p.coeff i : L) * (s ^ k * s ^ n i) = s ^ k * (s ^ n i * (p.coeff i : L)) by ring]
      exact mul_mem (pow_mem (Algebra.subset_adjoin hs) k) (hn i)
    · rcases (not_lt.mp hi).lt_or_eq with hlt | heq
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero, zero_mul]
        exact zero_mem _
      · rw [← heq, hmonic.coeff_natDegree, map_one, one_mul, Nat.sub_self, pow_zero]
        exact one_mem _
  have hlifts : q ∈ Polynomial.lifts (algebraMap (Algebra.adjoin K S) L) :=
    (Polynomial.lifts_iff_coeff_lifts q).mpr fun i => ⟨⟨q.coeff i, hqcoeff i⟩, rfl⟩
  obtain ⟨q', hq'q, -, hq'monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hqmonic
  refine ⟨N, (mem_chartRing_iff K).mpr ⟨q', hq'monic, ?_⟩⟩
  rw [Polynomial.eval₂_eq_eval_map, hq'q, hqroot]

end InvertGenerator

end CurveModel

end AlgebraicCurve
