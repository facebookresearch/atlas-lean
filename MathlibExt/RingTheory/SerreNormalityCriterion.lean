/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import MathlibExt.RingTheory.Depth.QuotSMulTop
import MathlibExt.RingTheory.RegularLocalRing.IsDomain
import MathlibExt.RingTheory.SerreCriterionReduced
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Serre's criterion for normality

Let `R` be a Noetherian ring. Call `R` normal if `R_p` is an integrally closed domain for every
prime `p`. We prove that `R` is normal if and only if it satisfies

* `(R₁)`: for every prime `p` with `p.height ≤ 1`, the localization `R_p` is a regular local
  ring (`IsRegularLocalRing`), and
* `(S₂)`: for every prime `p`, `min 2 (ringKrullDim R_p) ≤ depth R_p`.

Depth is Mathlib's `Ext`-based `IsLocalRing.depth` of `R_p` as a module over itself; for a
Noetherian local ring it equals the supremum of the lengths of regular sequences in the maximal
ideal (`IsLocalRing.depth_eq_sSup_length_isRegular`), as in the Stacks project. This is the same
depth notion as in `MathlibExt.RingTheory.SerreCriterionReduced`.

## Main results

* `IsLocalRing.two_le_depth_of_isIntegrallyClosed`: a normal Noetherian local domain of
  dimension `≥ 2` has depth `≥ 2`.
* `IsLocalRing.isRegularLocalRing_of_isIntegrallyClosed`: a normal Noetherian local domain of
  dimension `≤ 1` is regular.
* `IsRegularLocalRing.isIntegrallyClosed_of_ringKrullDim_le_one`: a regular local ring of
  dimension `≤ 1` is integrally closed.
* `isIntegrallyClosed_of_forall_isRegularLocalRing_and_min_two_le_depth`: a Noetherian ring with
  `(R₁)` and `(S₂)` is integrally closed in its total ring of fractions.
* `IsLocalRing.isDomain_of_isReduced_of_isIntegrallyClosed`: a reduced Noetherian local ring that
  is integrally closed in its total ring of fractions is a domain.
* `IsLocalRing.depth_self_eq_of_ringEquiv`: depth is invariant under ring isomorphisms.
* `forall_isIntegrallyClosed_localization_iff`: **Serre's criterion for normality**.
* `isIntegrallyClosed_iff_forall_isRegularLocalRing_and_min_two_le_depth`: the criterion for
  Noetherian domains, stated with `IsIntegrallyClosed R`.

## Proof

Normal implies `(R₁)` and `(S₂)`: a normal Noetherian local domain of dimension `≤ 1` is a field
or a Dedekind (hence discrete valuation) ring, so regular. In dimension `≥ 2`, take `x ≠ 0` in
the maximal ideal `𝔪`. If `𝔪` were associated to `A / x A`, say `𝔪 = (x A : y)` with `y ∉ x A`,
then `f = y / x` satisfies `f 𝔪 ⊆ A`; if `f 𝔪 ⊆ 𝔪` then `f` is integral (`𝔪` is a faithful
finitely generated module), so `f ∈ A`, impossible; otherwise `f 𝔪 = A` and `𝔪` is principal,
so `dim A ≤ 1` by Krull's height theorem. Hence `depth (A / x A) ≥ 1` and `depth A ≥ 2`.

`(R₁)` and `(S₂)` imply normal: if `a / b` (with `b` a nonzerodivisor) is integral over `R` and
`a ∉ b R`, an associated prime `P` of `R / b R` containing the annihilator of `a` satisfies
`depth R_P ≤ 1`, so `height P ≤ 1` by `(S₂)` and `R_P` is a regular local ring of dimension `≤ 1`
by `(R₁)`, hence integrally closed; so `a ∈ b R_P`, contradicting the choice of `P`. Thus `R` is
integrally closed in its total ring of fractions. Both properties pass to `R_p`, so each `R_p`
is integrally closed in its total ring of fractions, and reduced by Serre's criterion for
reducedness; a reduced local ring integrally closed in its total ring of fractions has no
nontrivial idempotent fractions, hence a single minimal prime, so it is a domain.

## References

* The Stacks project, Tag 031S (Lemma 10.157.4, Serre's criterion for normality); Tag 031P
  (Definition 10.157.1) for `(R_k)` and `(S_k)`; Tag 031R (Lemma 10.157.3) for reducedness.
  The proof of the depth bound in dimension `≥ 2` given here is a direct argument
  (EGA IV₂, Theorem 5.8.6, is the original reference); it does not follow the Stacks proof.
-/

@[expose] public section

universe u

open IsLocalRing Pointwise Polynomial

namespace SerreNormalityCriterion

variable {A : Type u} [CommRing A]

private lemma mk_eq_zero_iff {x y : A} :
    (Submodule.Quotient.mk y : QuotSMulTop x A) = 0 ↔ ∃ c, x * c = y := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
  simp [smul_eq_mul]

private lemma mem_colon_mk_iff {x y s : A} :
    s ∈ (⊥ : Submodule A (QuotSMulTop x A)).colon {Submodule.Quotient.mk y} ↔
      ∃ c, x * c = s * y := by
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
    mk_eq_zero_iff, smul_eq_mul]

private lemma le_one_of_not_two_le {d : WithBot ℕ∞} (h : ¬ 2 ≤ d) : d ≤ 1 := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd (WithBot.coe_le_coe.mpr le_top) h
    | coe n =>
      have : ¬ 2 ≤ n := fun h' ↦ h (WithBot.coe_le_coe.mpr (by exact_mod_cast h'))
      exact_mod_cast (by omega : n ≤ 1)

/-- If a monic `p` gives the homogeneous relation `(p.scaleRoots b).eval a = 0` in an integrally
closed domain and `b ≠ 0`, then `b` divides `a`. -/
private lemma exists_mul_eq_of_eval_scaleRoots [IsDomain A] [IsIntegrallyClosed A] {p : A[X]}
    (hp : p.Monic) {a b : A} (hb : b ≠ 0) (h : (p.scaleRoots b).eval a = 0) :
    ∃ c, b * c = a := by
  let K := FractionRing A
  have hinj := IsFractionRing.injective A K
  have hb' : algebraMap A K b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb
  have hroot : aeval (algebraMap A K a / algebraMap A K b) p = 0 := by
    have := Polynomial.scaleRoots_eval₂_mul (p := p) (algebraMap A K)
      (algebraMap A K a / algebraMap A K b) b
    rw [mul_div_cancel₀ _ hb', Polynomial.eval₂_at_apply, h, map_zero] at this
    rw [aeval_def]
    exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ hb')
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp ⟨p, hp, hroot⟩
  refine ⟨c, hinj ?_⟩
  rw [map_mul, hc, mul_div_cancel₀ _ hb']

end SerreNormalityCriterion

open SerreNormalityCriterion

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- A Noetherian local domain `A` that is not a field has `1 ≤ IsLocalRing.depth A` (`A` as a
module over itself): any nonzero element of the maximal ideal is a nonzerodivisor. -/
theorem one_le_depth_of_isDomain [IsDomain A] (h : ¬ IsField A) :
    1 ≤ IsLocalRing.depth (ModuleCat.of A A) := by
  have hm : maximalIdeal A ≠ ⊥ := fun h' ↦ h (isField_iff_maximalIdeal_eq.mpr h')
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  exact one_le_depth_iff.mpr ⟨x, hx, IsSMulRegular.of_ne_zero hx0⟩

/-- **A normal Noetherian local domain of dimension at least two has depth at least two.**
Let `A` be a Noetherian local domain that is integrally closed (`IsIntegrallyClosed A`) with
`2 ≤ ringKrullDim A`. Then `2 ≤ IsLocalRing.depth A`, where `A` is regarded as a module over
itself.

This is the depth part of the implication (1) ⇒ (2) of Stacks, Tag 031S (Lemma 10.157.4), whose
proof uses Lemma 10.119.2 there; the proof here is a direct one: for `0 ≠ x ∈ 𝔪`, the maximal
ideal is not associated to `A / x A` (otherwise `𝔪` is principal or `A` is not normal). -/
theorem two_le_depth_of_isIntegrallyClosed [IsDomain A] [IsIntegrallyClosed A]
    (hdim : 2 ≤ ringKrullDim A) : 2 ≤ IsLocalRing.depth (ModuleCat.of A A) := by
  have hfield : ¬ IsField A := fun h ↦ by
    rw [ringKrullDim_eq_zero_of_isField h] at hdim
    exact absurd hdim (by decide)
  have hm : maximalIdeal A ≠ ⊥ := fun h' ↦ hfield (isField_iff_maximalIdeal_eq.mpr h')
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hreg : IsSMulRegular A x := IsSMulRegular.of_ne_zero hx0
  rw [← depth_quotSMulTop_add_one hx hreg]
  suffices h1 : 1 ≤ IsLocalRing.depth (ModuleCat.of A (QuotSMulTop x A)) by
    rw [← one_add_one_eq_two]
    exact add_le_add_left h1 1
  have := nontrivial_quotSMulTop_of_mem_maximalIdeal A hx
  refine one_le_depth_iff.mpr ?_
  by_contra! hne
  -- The maximal ideal consists of zerodivisors on `A / x A`, so it is an associated prime.
  have hsub : (maximalIdeal A : Set A) ⊆
      ⋃ p ∈ associatedPrimes A (QuotSMulTop x A), (p : Set A) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    exact fun z hz ↦ hne z hz
  obtain ⟨P, hP, hle⟩ := (Ideal.subset_union_prime_finite (f := id)
    (associatedPrimes.finite A (QuotSMulTop x A)) ⊥ ⊥ (fun p hp _ _ ↦ hp.isPrime)).mp hsub
  obtain ⟨hPprime, ybar, hPy⟩ := isAssociatedPrime_iff.mp hP
  have hPm : P = maximalIdeal A := (le_maximalIdeal hPprime.ne_top).antisymm hle
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ ybar
  have hy : ¬ ∃ c, x * c = y := by
    intro hc
    apply hPprime.ne_top
    rw [hPy, mk_eq_zero_iff.mpr hc, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  have hmy : ∀ a ∈ maximalIdeal A, ∃ c, x * c = a * y := by
    intro a ha
    rw [← hPm, hPy] at ha
    exact mem_colon_mk_iff.mp ha
  by_cases hcase : ∃ a ∈ maximalIdeal A, ∃ c, x * c = a * y ∧ c ∉ maximalIdeal A
  · -- Then the maximal ideal is principal, so `dim A ≤ 1`.
    obtain ⟨a, ha, c, hc, hcm⟩ := hcase
    obtain ⟨u, rfl⟩ := notMem_maximalIdeal.mp hcm
    have hspan : maximalIdeal A = Ideal.span {a * ↑u⁻¹} := by
      apply le_antisymm
      · intro b hb
        obtain ⟨d, hd⟩ := hmy b hb
        rw [Ideal.mem_span_singleton']
        refine ⟨d, ?_⟩
        have h0 : x * (↑u * b - a * d) = 0 := by linear_combination b * hc - a * hd
        have h2 : ↑u * b = a * d := sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hx0)
        calc d * (a * ↑u⁻¹) = ↑u⁻¹ * (a * d) := by ring
          _ = ↑u⁻¹ * (↑u * b) := by rw [h2]
          _ = b := by rw [← mul_assoc, Units.inv_mul, one_mul]
      · rw [Ideal.span_singleton_le_iff_mem]
        exact Ideal.mul_mem_right _ _ ha
    have hle1 := ringKrullDim_le_spanFinrank_maximalIdeal A
    have hsf : (maximalIdeal A).spanFinrank ≤ 1 := by
      rw [hspan]
      by_cases ht : a * ↑u⁻¹ = 0
      · rw [ht, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.spanFinrank_bot]
        exact zero_le_one
      · exact (Submodule.spanFinrank_singleton ht).le
    have : ringKrullDim A ≤ 1 := hle1.trans (by exact_mod_cast hsf)
    exact absurd (hdim.trans this) (by decide)
  · -- Otherwise `y / x` is integral over `A`, hence lies in `A`.
    push Not at hcase
    let K := FractionRing A
    have hinj := IsFractionRing.injective A K
    have hx' : algebraMap A K x ≠ 0 := (map_ne_zero_iff _ hinj).mpr hx0
    let N : Submodule A K := Submodule.map (Algebra.linearMap A K) (maximalIdeal A)
    have hN : N ≠ ⊥ := (Submodule.ne_bot_iff N).mpr ⟨_, ⟨x, hx, rfl⟩, hx'⟩
    have hNfg : N.FG := (IsNoetherian.noetherian _).map _
    have hint : IsIntegral A (algebraMap A K y / algebraMap A K x) := by
      refine isIntegral_of_smul_mem_submodule N hN hNfg _ ?_
      rintro n ⟨a, ha, rfl⟩
      obtain ⟨c, hc⟩ := hmy a ha
      refine ⟨c, hcase a ha c hc, ?_⟩
      have hc' := congrArg (algebraMap A K) hc
      rw [map_mul, map_mul] at hc'
      simp only [Algebra.linearMap_apply, smul_eq_mul]
      field_simp
      linear_combination hc'
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine hy ⟨r, hinj ?_⟩
    rw [map_mul, hr, mul_div_cancel₀ _ hx']

/-- A normal Noetherian local domain `A` satisfies `min 2 (ringKrullDim A) ≤ depth A`
(property `(S₂)` at the maximal ideal; Stacks, Tag 031S, proof of (1) ⇒ (2)). -/
theorem min_two_le_depth_of_isIntegrallyClosed [IsDomain A] [IsIntegrallyClosed A] :
    min 2 (ringKrullDim A) ≤
      ((IsLocalRing.depth (ModuleCat.of A A) : ℕ∞) : WithBot ℕ∞) := by
  by_cases h2 : 2 ≤ ringKrullDim A
  · exact (min_le_left _ _).trans
      (WithBot.coe_le_coe.mpr (two_le_depth_of_isIntegrallyClosed h2))
  by_cases hf : IsField A
  · rw [ringKrullDim_eq_zero_of_isField hf]
    exact (min_le_right _ _).trans (WithBot.coe_le_coe.mpr zero_le)
  · exact (min_le_right _ _).trans ((le_one_of_not_two_le h2).trans
      (WithBot.coe_le_coe.mpr (one_le_depth_of_isDomain hf)))

/-- A normal Noetherian local domain `A` with `ringKrullDim A ≤ 1` is a regular local ring:
it is a field or a discrete valuation ring (Stacks, Tag 031S, proof of (1) ⇒ (2), case
`d = 1`; there via Lemma 10.119.7). -/
theorem isRegularLocalRing_of_isIntegrallyClosed [IsDomain A] [IsIntegrallyClosed A]
    (h : ringKrullDim A ≤ 1) : IsRegularLocalRing A := by
  by_cases hf : IsField A
  · refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le A ?_
    rw [isField_iff_maximalIdeal_eq.mp hf, Submodule.spanFinrank_bot]
    exact_mod_cast ringKrullDim_nonneg_of_nontrivial
  · have hm1 : (maximalIdeal A).height ≤ 1 := by
      rw [← maximalIdeal_height_eq_ringKrullDim] at h
      exact_mod_cast h
    have : Ring.DimensionLEOne A := ⟨fun {p} hp0 hp ↦ by
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (I := ⊥) (J := p)
        (bot_lt_iff_ne_bot.mpr hp0)
      rw [Ideal.height_bot, zero_add] at h1
      by_contra hpm
      have hlt : p < maximalIdeal A :=
        lt_of_le_of_ne (le_maximalIdeal hp.ne_top) (fun h ↦ hpm (h ▸ inferInstance))
      have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      have h3 : (2 : ℕ∞) ≤ 1 := by
        calc (2 : ℕ∞) = 1 + 1 := by norm_num
          _ ≤ p.height + 1 := by gcongr
          _ ≤ _ := h2
          _ ≤ 1 := hm1
      exact absurd h3 (by norm_num)⟩
    have : IsDedekindDomain A := { }
    have : IsDiscreteValuationRing A :=
      ((IsDiscreteValuationRing.TFAE A hf).out 3 1).mp (inferInstance : IsDedekindDomain A)
    infer_instance

end IsLocalRing

namespace IsRegularLocalRing

/-- A regular local ring `A` with `ringKrullDim A ≤ 1` is integrally closed: its maximal
ideal is generated by at most one element, so `A` is a field or a discrete valuation ring. -/
theorem isIntegrallyClosed_of_ringKrullDim_le_one {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (h : ringKrullDim A ≤ 1) : IsIntegrallyClosed A := by
  have := IsRegularLocalRing.isDomain A
  have hle : (maximalIdeal A).spanFinrank ≤ 1 := by
    have h' := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [← h'] at h
    exact_mod_cast h
  by_cases hf : IsField A
  · let := hf.toField
    infer_instance
  · have hprin : (maximalIdeal A).IsPrincipal := by
      obtain ⟨s, hs, hspan⟩ :=
        (IsNoetherian.noetherian (maximalIdeal A)).exists_span_finset_card_eq_spanFinrank
      obtain ⟨t, ht⟩ := Finset.card_le_one_iff_subset_singleton.mp (hs ▸ hle)
      rcases Finset.subset_singleton_iff.mp ht with rfl | rfl
      · rw [← hspan]
        exact ⟨⟨0, by simp⟩⟩
      · rw [← hspan]
        exact ⟨⟨t, by simp⟩⟩
    have : IsDiscreteValuationRing A :=
      ((IsDiscreteValuationRing.TFAE A hf).out 5 1).mp hprin
    infer_instance

end IsRegularLocalRing

namespace SerreNormalityCriterion

variable {R : Type u} [CommRing R]

/-- Let `R` be a Noetherian ring, `b` a nonzerodivisor of `R` and `P` a prime of the form
`(b R : y)` (that is, `P` is an associated prime of `R / b R`). Then `depth R_P ≤ 1`. -/
private lemma depth_le_one_of_eq_colon [IsNoetherianRing R] {b y : R} (hb : b ∈ nonZeroDivisors R)
    {P : Ideal R} [P.IsPrime]
    (hPy : P = (⊥ : Submodule R (QuotSMulTop b R)).colon {Submodule.Quotient.mk y}) :
    IsLocalRing.depth (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) ≤ 1 := by
  set L := Localization.AtPrime P
  have hbP : b ∈ P := by
    rw [hPy, mem_colon_mk_iff]
    exact ⟨y, by ring⟩
  have hbm : algebraMap R L b ∈ maximalIdeal L :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L P b).mpr hbP
  have hreg : IsSMulRegular L (algebraMap R L b) := by
    have hb' := IsLocalization.map_nonZeroDivisors_le P.primeCompl L ⟨b, hb, rfl⟩
    intro u v huv
    simp only [smul_eq_mul] at huv
    exact sub_eq_zero.mp (mem_nonZeroDivisors_iff_right.mp hb' _ (by linear_combination huv))
  rw [← depth_quotSMulTop_add_one hbm hreg]
  suffices h0 : ¬ 1 ≤ IsLocalRing.depth (ModuleCat.of L (QuotSMulTop (algebraMap R L b) L)) by
    rw [Order.lt_one_iff.mp (not_le.mp h0), zero_add]
  have := nontrivial_quotSMulTop_of_mem_maximalIdeal L hbm
  rw [one_le_depth_iff]
  rintro ⟨z, hz, hzreg⟩
  obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl z
  have hs : s ∈ P := (IsLocalization.AtPrime.mk'_mem_maximal_iff L P s t).mp hz
  obtain ⟨c, hc⟩ := mem_colon_mk_iff.mp (hPy ▸ hs)
  have hsreg : IsSMulRegular (QuotSMulTop (algebraMap R L b) L) (algebraMap R L s) := by
    rw [← IsLocalization.mk'_spec L s t]
    exact hzreg.mul ((IsLocalization.map_units L t).isSMulRegular _)
  have hy0 : (Submodule.Quotient.mk (algebraMap R L y) : QuotSMulTop (algebraMap R L b) L) = 0 := by
    apply hsreg
    beta_reduce
    rw [smul_zero, ← Submodule.Quotient.mk_smul, mk_eq_zero_iff]
    exact ⟨algebraMap R L c, by rw [smul_eq_mul, ← map_mul, ← map_mul, hc]⟩
  obtain ⟨d, hd⟩ := mk_eq_zero_iff.mp hy0
  obtain ⟨⟨r, t'⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl d
  have hbr : algebraMap R L (b * r) = algebraMap R L (t' * y) := by
    rw [map_mul, map_mul, ← hd, mul_comm (algebraMap R L t'), mul_assoc,
      IsLocalization.mk'_spec]
  obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists P.primeCompl L).mp hbr
  refine (P.primeCompl.mul_mem u.2 t'.2) ((SetLike.ext_iff.mp hPy _).mpr
    (mem_colon_mk_iff.mpr ⟨u * r, ?_⟩))
  linear_combination hu

end SerreNormalityCriterion

open SerreNormalityCriterion

/-- **`(R₁)` and `(S₂)` imply normality** (Stacks, Tag 031S, Lemma 10.157.4, the implication
(2) ⇒ (1), in the form of its key step). Let `R` be a Noetherian ring such that

* `(R₁)`: for every prime `p` with `p.height ≤ 1`, `R_p` is a regular local ring, and
* `(S₂)`: for every prime `p`, `min 2 (ringKrullDim R_p) ≤ IsLocalRing.depth R_p`.

Then `R` is integrally closed in its total ring of fractions (`IsIntegrallyClosed R`, which
Mathlib defines through `FractionRing R`, the localization at all nonzerodivisors).

Proof: if `a / b` is integral with `b` a nonzerodivisor and `a ∉ b R`, take an associated prime
`P` of `R / b R` containing the annihilator of the class of `a`. Then `depth R_P ≤ 1`, so
`(S₂)` forces `height P ≤ 1`, and by `(R₁)` the ring `R_P` is regular of dimension `≤ 1`, hence
a field or a discrete valuation ring, so integrally closed; then `a ∈ b R_P`, contradicting the
choice of `P`. -/
theorem isIntegrallyClosed_of_forall_isRegularLocalRing_and_min_two_le_depth
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hR1 : ∀ (p : Ideal R) [p.IsPrime], p.height ≤ 1 →
      IsRegularLocalRing (Localization.AtPrime p))
    (hS2 : ∀ (p : Ideal R) [p.IsPrime], min 2 (ringKrullDim (Localization.AtPrime p)) ≤
      ((IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) :
        ℕ∞) : WithBot ℕ∞)) :
    IsIntegrallyClosed R := by
  let K := FractionRing R
  have hinj : Function.Injective (algebraMap R K) := IsLocalization.injective K le_rfl
  rw [isIntegrallyClosed_iff K]
  intro f hf
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) f
  obtain ⟨p, hpm, hpe⟩ := hf
  -- The homogeneous form of the integral equation.
  have hrel : (p.scaleRoots (b : R)).eval a = 0 := by
    have := Polynomial.scaleRoots_eval₂_mul (p := p) (algebraMap R K)
      (IsLocalization.mk' K a b) b
    rw [IsLocalization.mk'_spec', Polynomial.eval₂_at_apply, hpe, mul_zero] at this
    exact hinj (by rw [this, map_zero])
  by_contra hne
  have ha : ¬ ∃ c, (b : R) * c = a := fun ⟨c, hc⟩ ↦
    hne ⟨c, (IsLocalization.mk'_eq_iff_eq_mul.mpr (by rw [← hc, map_mul, mul_comm])).symm⟩
  have hā : (Submodule.Quotient.mk a : QuotSMulTop (b : R) R) ≠ 0 :=
    fun h ↦ ha (mk_eq_zero_iff.mp h)
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hā
  obtain ⟨hPp, ybar, hPy⟩ := isAssociatedPrime_iff.mp hP
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ ybar
  set L := Localization.AtPrime P
  have hdep := depth_le_one_of_eq_colon b.2 hPy
  have hht : P.height ≤ 1 := by
    have h := (hS2 P).trans (WithBot.coe_le_coe.mpr hdep)
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P L] at h
    rcases min_le_iff.mp h with h | h
    · exact absurd h (by decide)
    · exact_mod_cast h
  have := hR1 P hht
  have := IsRegularLocalRing.isDomain L
  have : IsIntegrallyClosed L :=
    IsRegularLocalRing.isIntegrallyClosed_of_ringKrullDim_le_one
      (by rw [IsLocalization.AtPrime.ringKrullDim_eq_height P L]; exact_mod_cast hht)
  let φ := algebraMap R L
  have hb0 : φ b ≠ 0 :=
    nonZeroDivisors.ne_zero (IsLocalization.map_nonZeroDivisors_le P.primeCompl L ⟨b, b.2, rfl⟩)
  obtain ⟨c, hc⟩ := exists_mul_eq_of_eval_scaleRoots (hpm.map φ) hb0 (a := φ a) (by
      rw [← Polynomial.map_scaleRoots _ _ _ (by rw [hpm.leadingCoeff, map_one]; exact one_ne_zero),
        Polynomial.eval_map, Polynomial.eval₂_at_apply, hrel, map_zero])
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
  have has : φ (b * r) = φ (s * a) := by
    rw [map_mul, map_mul, ← hc, mul_comm (φ s), mul_assoc, IsLocalization.mk'_spec]
  obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists P.primeCompl L).mp has
  apply P.primeCompl.mul_mem u.2 s.2
  apply hle
  rw [mem_colon_mk_iff]
  exact ⟨u * r, by linear_combination hu⟩

/-- **Normality implies `(R₁)` and `(S₂)`** (Stacks, Tag 031S, Lemma 10.157.4, (1) ⇒ (2)).
Let `R` be a Noetherian ring such that every localization `R_p` at a prime is an integrally
closed domain. Then

* `(R₁)`: `R_p` is a regular local ring for every prime `p` with `p.height ≤ 1`, and
* `(S₂)`: `min 2 (ringKrullDim R_p) ≤ IsLocalRing.depth R_p` for every prime `p` (with `R_p` a
  module over itself; the inequality is in `WithBot ℕ∞`).

The properties are those of Tag 031P, with "regular" meaning `IsRegularLocalRing`. -/
theorem forall_isRegularLocalRing_and_min_two_le_depth_of_isIntegrallyClosed_localization
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (h : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    (∀ (p : Ideal R) [p.IsPrime], p.height ≤ 1 →
      IsRegularLocalRing (Localization.AtPrime p)) ∧
    (∀ (p : Ideal R) [p.IsPrime], min 2 (ringKrullDim (Localization.AtPrime p)) ≤
      ((IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) :
        ℕ∞) : WithBot ℕ∞)) := by
  refine ⟨fun p _ hp ↦ ?_, fun p _ ↦ ?_⟩
  · obtain ⟨_, _⟩ := h p
    exact IsLocalRing.isRegularLocalRing_of_isIntegrallyClosed
      (by rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]; exact_mod_cast hp)
  · obtain ⟨_, _⟩ := h p
    exact IsLocalRing.min_two_le_depth_of_isIntegrallyClosed

/-- **Serre's criterion for normality, for Noetherian domains** (Stacks, Tag 031S,
Lemma 10.157.4, for a domain). A Noetherian domain `R` is integrally closed if and only if it
has `(R₁)` (`R_p` is a regular local ring for every prime `p` with `p.height ≤ 1`) and `(S₂)`
(`min 2 (ringKrullDim R_p) ≤ IsLocalRing.depth R_p` for every prime `p`). For a domain,
`IsIntegrallyClosed R` is equivalent to normality in the sense of Stacks (every `R_p` is a
normal domain), see `forall_isIntegrallyClosed_localization_iff_of_isDomain`. -/
theorem isIntegrallyClosed_iff_forall_isRegularLocalRing_and_min_two_le_depth
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] :
    IsIntegrallyClosed R ↔
      (∀ (p : Ideal R) [p.IsPrime], p.height ≤ 1 →
        IsRegularLocalRing (Localization.AtPrime p)) ∧
      (∀ (p : Ideal R) [p.IsPrime], min 2 (ringKrullDim (Localization.AtPrime p)) ≤
        ((IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) :
          ℕ∞) : WithBot ℕ∞)) := by
  refine ⟨fun _ ↦ ?_, fun ⟨h1, h2⟩ ↦
    isIntegrallyClosed_of_forall_isRegularLocalRing_and_min_two_le_depth h1 h2⟩
  refine forall_isRegularLocalRing_and_min_two_le_depth_of_isIntegrallyClosed_localization
    fun p _ ↦ ⟨inferInstance, ?_⟩
  exact isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors

/-- **Serre's criterion for normality, for Noetherian domains, in the printed form.** A
Noetherian domain `R` has every localization `R_p` at a prime an integrally closed domain if and
only if it has `(R₁)` and `(S₂)`. This is the special case of
`forall_isIntegrallyClosed_localization_iff` for domains, with a shorter proof. -/
theorem forall_isIntegrallyClosed_localization_iff_of_isDomain
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] :
    (∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ↔
      (∀ (p : Ideal R) [p.IsPrime], p.height ≤ 1 →
        IsRegularLocalRing (Localization.AtPrime p)) ∧
      (∀ (p : Ideal R) [p.IsPrime], min 2 (ringKrullDim (Localization.AtPrime p)) ≤
        ((IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) :
          ℕ∞) : WithBot ℕ∞)) := by
  refine ⟨forall_isRegularLocalRing_and_min_two_le_depth_of_isIntegrallyClosed_localization,
    fun h ↦ ?_⟩
  have := isIntegrallyClosed_iff_forall_isRegularLocalRing_and_min_two_le_depth.mpr h
  exact fun p _ ↦ ⟨inferInstance,
    isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors⟩

namespace SerreNormalityCriterion

variable {A : Type u} [CommRing A]

/-- In a reduced ring, an element lying in every minimal prime is zero. -/
private lemma eq_zero_of_forall_mem_minimalPrimes [IsReduced A] {x : A}
    (h : ∀ q ∈ minimalPrimes A, x ∈ q) : x = 0 := by
  have hmem : x ∈ sInf ((⊥ : Ideal A).minimalPrimes) := Submodule.mem_sInf.mpr h
  rw [Ideal.sInf_minimalPrimes] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact IsReduced.eq_zero x ⟨n, by simpa using hn⟩

end SerreNormalityCriterion

open SerreNormalityCriterion

/-- A Noetherian local ring that is reduced and integrally closed in its total ring of fractions
is a domain.

If `q₁ ≠ q₂` were two minimal primes, choose `a` in every minimal prime except `q₁` and `a'` in
`q₁` but in no other minimal prime. Then `b = a + a'` is a nonzerodivisor, `a a' = 0`, and
`a / b` is an idempotent of the total ring of fractions, hence integral, hence of the form `c`
with `a = b c`. Since `A` is local, `c` or `1 - c` is a unit, and either case contradicts
`a (1 - c) = a' c`. -/
theorem IsLocalRing.isDomain_of_isReduced_of_isIntegrallyClosed {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsReduced A] [IsIntegrallyClosed A] : IsDomain A := by
  classical
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  obtain ⟨q1, hq1, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A))
    (J := maximalIdeal A) bot_le
  have hq1p : q1.IsPrime := hq1.1.1
  by_cases hone : ∀ q ∈ minimalPrimes A, q = q1
  · have hbot : q1 = ⊥ := by
      refine eq_bot_iff.mpr fun x hx ↦ ?_
      exact eq_zero_of_forall_mem_minimalPrimes fun q hq ↦ hone q hq ▸ hx
    have : (⊥ : Ideal A).IsPrime := hbot ▸ hq1p
    exact IsDomain.of_bot_isPrime A
  push Not at hone
  obtain ⟨q2, hq2, hne⟩ := hone
  exfalso
  set S := hfin.toFinset.erase q1
  have hmemS : ∀ q, q ∈ S ↔ q ∈ minimalPrimes A ∧ q ≠ q1 := fun q ↦ by
    rw [Finset.mem_erase, Set.Finite.mem_toFinset, and_comm]
  have hmin : ∀ q ∈ minimalPrimes A, q ≤ q1 → q = q1 := fun q hq hle ↦
    le_antisymm hle (hq1.2 ⟨hq.1.1, bot_le⟩ hle)
  have hmin' : ∀ q ∈ minimalPrimes A, q1 ≤ q → q = q1 := fun q hq hle ↦
    (le_antisymm hle (hq.2 ⟨hq1p, bot_le⟩ hle)).symm
  -- `a` lies in every minimal prime except `q₁`.
  have h1 : ¬ S.inf id ≤ q1 := by
    intro h
    obtain ⟨q, hq, hle⟩ := (Ideal.IsPrime.inf_le' hq1p).mp h
    exact ((hmemS q).mp hq).2 (hmin q ((hmemS q).mp hq).1 hle)
  obtain ⟨a, haS, haq1⟩ := IsConcreteLE.not_le_iff_exists.mp h1
  have haq : ∀ q ∈ minimalPrimes A, q ≠ q1 → a ∈ q := fun q hq hq' ↦
    Finset.inf_le (f := id) ((hmemS q).mpr ⟨hq, hq'⟩) haS
  -- `a'` lies in `q₁` but in no other minimal prime.
  have h2 : ¬ (q1 : Set A) ⊆ ⋃ q ∈ (S : Set (Ideal A)), (q : Set A) := by
    intro h
    obtain ⟨q, hq, hle⟩ := (Ideal.subset_union_prime_finite (f := id) S.finite_toSet ⊥ ⊥
      (fun q hq _ _ ↦ ((hmemS q).mp hq).1.1.1)).mp h
    exact ((hmemS q).mp hq).2 (hmin' q ((hmemS q).mp hq).1 hle)
  obtain ⟨a', ha'q1, ha'S⟩ := Set.not_subset.mp h2
  have ha'q : ∀ q ∈ minimalPrimes A, q ≠ q1 → a' ∉ q := fun q hq hq' h ↦
    ha'S (Set.mem_biUnion (x := q) (by simpa using (hmemS q).mpr ⟨hq, hq'⟩) h)
  -- `b = a + a'` is a nonzerodivisor and `a a' = 0`.
  have hb : a + a' ∈ nonZeroDivisors A := by
    refine mem_nonZeroDivisors_iff_right.mpr fun x hx ↦ ?_
    refine eq_zero_of_forall_mem_minimalPrimes fun q hq ↦ ?_
    have hxq : x * (a + a') ∈ q := hx ▸ q.zero_mem
    refine (hq.1.1.mem_or_mem hxq).resolve_right fun hab ↦ ?_
    by_cases hq' : q = q1
    · subst hq'
      exact haq1 ((q.add_mem_iff_left ha'q1).mp hab)
    · exact ha'q q hq hq' ((q.add_mem_iff_right (haq q hq hq')).mp hab)
  have haa' : a * a' = 0 := by
    refine eq_zero_of_forall_mem_minimalPrimes fun q hq ↦ ?_
    by_cases hq' : q = q1
    · exact q.mul_mem_left _ (hq' ▸ ha'q1)
    · exact q.mul_mem_right _ (haq q hq hq')
  -- `a / b` is an idempotent of the total ring of fractions.
  let K := FractionRing A
  have hinj : Function.Injective (algebraMap A K) := IsLocalization.injective K le_rfl
  set e : K := IsLocalization.mk' K a ⟨a + a', hb⟩
  have hbe : algebraMap A K (a + a') * e = algebraMap A K a := IsLocalization.mk'_spec' K _ _
  have hbu : IsUnit (algebraMap A K (a + a')) :=
    IsLocalization.map_units K (⟨a + a', hb⟩ : nonZeroDivisors A)
  have hidem : e * (e - 1) = 0 := by
    have h0 : algebraMap A K (a + a') ^ 2 * (e * (e - 1)) = 0 := by
      have : algebraMap A K (a + a') ^ 2 * (e * (e - 1)) =
          algebraMap A K a * (algebraMap A K a - algebraMap A K (a + a')) := by
        rw [← hbe]
        ring
      rw [this, ← map_sub, ← map_mul, show a * (a - (a + a')) = -(a * a') by ring, haa',
        neg_zero, map_zero]
    exact (hbu.pow 2).mul_right_eq_zero.mp h0
  have hint : IsIntegral A e := by
    refine ⟨X * (X - C 1), monic_X.mul (monic_X_sub_C 1), ?_⟩
    simpa [eval₂_mul, eval₂_sub] using hidem
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hac : (a + a') * c = a := hinj (by rw [map_mul, hc, hbe])
  have key : a * (1 - c) = a' * c := by linear_combination -hac
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with hu | hu
  · have hq2p : q2.IsPrime := hq2.1.1
    have : a' * c ∈ q2 := key ▸ q2.mul_mem_right _ (haq q2 hq2 hne)
    rcases hq2p.mem_or_mem this with h | h
    · exact ha'q q2 hq2 hne h
    · exact hq2p.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  · have : a * (1 - c) ∈ q1 := key ▸ q1.mul_mem_right _ ha'q1
    rcases hq1p.mem_or_mem this with h | h
    · exact haq1 h
    · exact hq1p.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)

namespace IsLocalRing

open RingTheory.Sequence

variable {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]

/-- Lengths of regular sequences in the maximal ideal are transported along a ring
isomorphism. -/
private lemma lengths_subset_of_ringEquiv (e : A ≃+* B) :
    {(List.length rs : ℕ∞) | (rs : List A)
      (_ : IsRegular (ModuleCat.of A A) rs) (_ : ∀ r ∈ rs, r ∈ maximalIdeal A)} ⊆
    {(List.length rs : ℕ∞) | (rs : List B)
      (_ : IsRegular (ModuleCat.of B B) rs) (_ : ∀ r ∈ rs, r ∈ maximalIdeal B)} := by
  rintro n ⟨rs, reg, mem, rfl⟩
  refine ⟨rs.map e, ?_, ?_, by simp⟩
  · refine (AddEquiv.isRegular_congr (M := A) (M₂ := B) (e := e.toAddEquiv) ?_).mp reg
    exact List.forall₂_map_right_iff.mpr <| List.forall₂_same.mpr fun r _ x ↦ by
      simp [smul_eq_mul]
  · intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    have := mem a ha
    rw [mem_maximalIdeal, mem_nonunits_iff] at this ⊢
    simpa using this

/-- **Depth is invariant under ring isomorphisms.** If `e : A ≃+* B` is an isomorphism of
Noetherian local rings, then `IsLocalRing.depth A = IsLocalRing.depth B`, each ring regarded as a
module over itself. -/
theorem depth_self_eq_of_ringEquiv [IsNoetherianRing A] [IsNoetherianRing B] (e : A ≃+* B) :
    IsLocalRing.depth (ModuleCat.of A A) = IsLocalRing.depth (ModuleCat.of B B) := by
  rw [depth_eq_sSup_length_isRegular, depth_eq_sSup_length_isRegular]
  exact le_antisymm (sSup_le_sSup (lengths_subset_of_ringEquiv e))
    (sSup_le_sSup (lengths_subset_of_ringEquiv e.symm))

end IsLocalRing

namespace SerreNormalityCriterion

/-- **`(R₁)` and `(S₂)` pass to localizations at primes.** Let `R` be a Noetherian ring with
`(R₁)` and `(S₂)` and let `p` be a prime of `R`. Then `R_p` has `(R₁)` and `(S₂)`: for a prime
`q` of `R_p` with contraction `q'` to `R`, the local rings `(R_p)_q` and `R_{q'}` are
isomorphic, and regularity, dimension and depth are invariant under ring isomorphisms. -/
theorem localization_atPrime {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hR1 : ∀ (p : Ideal R) [p.IsPrime], p.height ≤ 1 →
      IsRegularLocalRing (Localization.AtPrime p))
    (hS2 : ∀ (p : Ideal R) [p.IsPrime], min 2 (ringKrullDim (Localization.AtPrime p)) ≤
      ((IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) :
        ℕ∞) : WithBot ℕ∞))
    (p : Ideal R) [p.IsPrime] :
    (∀ (q : Ideal (Localization.AtPrime p)) [q.IsPrime], q.height ≤ 1 →
      IsRegularLocalRing (Localization.AtPrime q)) ∧
    (∀ (q : Ideal (Localization.AtPrime p)) [q.IsPrime],
      min 2 (ringKrullDim (Localization.AtPrime q)) ≤
      ((IsLocalRing.depth (ModuleCat.of (Localization.AtPrime q) (Localization.AtPrime q)) :
        ℕ∞) : WithBot ℕ∞)) := by
  have key : ∀ (q : Ideal (Localization.AtPrime p)) [q.IsPrime],
      ∃ (q' : Ideal R) (_ : q'.IsPrime) (e : Localization.AtPrime q' ≃+* Localization.AtPrime q),
        ringKrullDim (Localization.AtPrime q') = ringKrullDim (Localization.AtPrime q) := by
    intro q _
    let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization p.primeCompl q
    exact ⟨_, inferInstance, e.toRingEquiv, ringKrullDim_eq_of_ringEquiv e.toRingEquiv⟩
  refine ⟨fun q _ hq ↦ ?_, fun q _ ↦ ?_⟩
  · obtain ⟨q', _, e, he⟩ := key q
    have : q'.height ≤ 1 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height q' (Localization.AtPrime q'),
        IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)] at he
      rw [WithBot.coe_inj.mp he]
      exact hq
    have := hR1 q' this
    exact IsRegularLocalRing.of_ringEquiv e
  · obtain ⟨q', _, e, he⟩ := key q
    rw [← he, ← IsLocalRing.depth_self_eq_of_ringEquiv e]
    exact hS2 q'

end SerreNormalityCriterion

open SerreNormalityCriterion

/-- **Serre's criterion for normality** (Stacks, Tag 031S, Lemma 10.157.4). Let `R` be a
Noetherian ring. Then every localization `R_p` of `R` at a prime is an integrally closed domain
(i.e. `R` is normal, Stacks Definition 10.37.11) if and only if `R` has

* `(R₁)`: for every prime `p` with `p.height ≤ 1`, `R_p` is a regular local ring
  (`IsRegularLocalRing`), and
* `(S₂)`: for every prime `p`, `min 2 (ringKrullDim R_p) ≤ IsLocalRing.depth R_p`, where `R_p` is
  regarded as a module over itself and the inequality is taken in `WithBot ℕ∞`.

Depth is Mathlib's `Ext`-based `IsLocalRing.depth`, which for the Noetherian local ring `R_p`
equals the supremum of the lengths of regular sequences in its maximal ideal
(`IsLocalRing.depth_eq_sSup_length_isRegular`), the definition used in the source. The
properties `(R₁)` and `(S₂)` are those of Tag 031P. No hypothesis of the printed statement is
dropped. -/
theorem forall_isIntegrallyClosed_localization_iff {R : Type u} [CommRing R] [IsNoetherianRing R] :
    (∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ↔
      (∀ (p : Ideal R) [p.IsPrime], p.height ≤ 1 →
        IsRegularLocalRing (Localization.AtPrime p)) ∧
      (∀ (p : Ideal R) [p.IsPrime], min 2 (ringKrullDim (Localization.AtPrime p)) ≤
        ((IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) :
          ℕ∞) : WithBot ℕ∞)) := by
  refine ⟨forall_isRegularLocalRing_and_min_two_le_depth_of_isIntegrallyClosed_localization,
    fun ⟨hR1, hS2⟩ p _ ↦ ?_⟩
  obtain ⟨h1, h2⟩ := localization_atPrime hR1 hS2 p
  set A := Localization.AtPrime p
  have hred : IsReduced A := by
    refine isReduced_iff_forall_isRegularLocalRing_and_min_one_le_depth.mpr
      ⟨fun q _ hq ↦ h1 q (by rw [hq]; exact zero_le_one), fun q _ ↦ ?_⟩
    refine le_trans ?_ (h2 q)
    exact min_le_min_right _ (by exact_mod_cast (one_le_two : (1 : ℕ∞) ≤ 2))
  have hic : IsIntegrallyClosed A :=
    isIntegrallyClosed_of_forall_isRegularLocalRing_and_min_two_le_depth h1 h2
  exact ⟨IsLocalRing.isDomain_of_isReduced_of_isIntegrallyClosed, hic⟩
