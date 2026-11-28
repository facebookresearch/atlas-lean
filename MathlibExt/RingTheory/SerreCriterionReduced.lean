/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import MathlibExt.RingTheory.Depth.QuotSMulTop
import MathlibExt.RingTheory.RegularLocalRing.IsDomain
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Serre's criterion for reducedness

Let `R` be a Noetherian ring. We prove that `R` is reduced if and only if it satisfies

* `(R₀)`: for every prime `p` of height `0`, the localization `R_p` is a regular local ring, and
* `(S₁)`: for every prime `p`, `depth R_p ≥ min (1, dim R_p)`.

Here `depth R_p` is Mathlib's `IsLocalRing.depth` of `R_p` as a module over itself (defined via
`Ext`; for a Noetherian local ring it equals the supremum of the lengths of regular sequences in
the maximal ideal, `IsLocalRing.depth_eq_sSup_length_isRegular`), `dim R_p` is `ringKrullDim`,
and "regular local ring" is `IsRegularLocalRing`.

## Main results

* `isReduced_iff_forall_isRegularLocalRing_and_min_one_le_depth`: Serre's criterion.

## Proof

If `R` is reduced, a localization at a minimal prime is a reduced zero-dimensional Noetherian
local ring, hence a field. If `dim R_p ≥ 1`, prime avoidance gives an element of the maximal
ideal of `R_p` outside all (finitely many) minimal primes, and in a reduced ring such an element
is a nonzerodivisor, so `depth R_p ≥ 1`.

Conversely, let `x ≠ 0` be nilpotent and let `P` be an associated prime containing its
annihilator. Condition `(S₁)` forbids `P` from having positive height: otherwise the maximal
ideal of `R_P` would contain a nonzerodivisor, while every element of `P R_P` is a zerodivisor
on the image of an element whose annihilator has radical `P`. So `P` is minimal, `R_P` is a
regular local ring by `(R₀)`, hence a domain, so the image of `x` in `R_P` vanishes, contradicting
that the annihilator of `x` lies in `P`.

## References

* The Stacks project, Tag 031R (Lemma 10.157.3); Tag 031P (Definition 10.157.1) for the
  properties `(R_k)` and `(S_k)`; Tag 00LE (Definition 10.72.1) for depth.
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerreCriterionReduced

variable {A : Type u} [CommRing A]

/-- In a reduced ring, an element lying in no minimal prime is a nonzerodivisor. -/
private lemma isSMulRegular_of_forall_notMem [IsReduced A] {x : A}
    (h : ∀ q ∈ minimalPrimes A, x ∉ q) : IsSMulRegular A x := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro y hy
  have hmem : y ∈ sInf ((⊥ : Ideal A).minimalPrimes) := by
    refine Submodule.mem_sInf.mpr fun q hq ↦ ?_
    have hxy : x * y ∈ q := by rw [smul_eq_mul] at hy; rw [hy]; exact q.zero_mem
    exact (hq.1.1.mem_or_mem hxy).resolve_left (h q hq)
  rw [Ideal.sInf_minimalPrimes] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact IsReduced.eq_zero y ⟨n, by simpa using hn⟩

/-- A reduced Noetherian local ring whose maximal ideal has nonzero height has a nonzerodivisor
in its maximal ideal. -/
private lemma exists_isSMulRegular_of_height_ne_zero [IsLocalRing A] [IsNoetherianRing A]
    [IsReduced A] (h : (maximalIdeal A).height ≠ 0) :
    ∃ x ∈ maximalIdeal A, IsSMulRegular A x := by
  have hnot : ¬ ((maximalIdeal A : Set A) ⊆ ⋃ q ∈ minimalPrimes A, (q : Set A)) := by
    intro hsub
    obtain ⟨q, hq, hle⟩ := (Ideal.subset_union_prime_finite (f := id)
      (minimalPrimes.finite_of_isNoetherianRing A) ⊥ ⊥ (fun q hq _ _ ↦ hq.1.1)).mp hsub
    have heq : q = maximalIdeal A := le_antisymm (le_maximalIdeal hq.1.1.ne_top) hle
    exact h (Ideal.height_eq_zero_iff.mpr (heq ▸ hq))
  obtain ⟨x, hx, hxq⟩ := Set.not_subset.mp hnot
  refine ⟨x, hx, isSMulRegular_of_forall_notMem fun q hq hxq' ↦ hxq ?_⟩
  exact Set.mem_biUnion hq hxq'

/-- If the annihilator of `t` lies in the prime `P`, then `t` has nonzero image in `R_P`. -/
private lemma algebraMap_ne_zero_of_colon_le {P : Ideal A} [P.IsPrime] {t : A}
    (h : (⊥ : Submodule A A).colon {t} ≤ P) :
    algebraMap A (Localization.AtPrime P) t ≠ 0 := by
  intro ht
  obtain ⟨⟨s, hs⟩, hst⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ t).mp ht
  exact hs (h (Submodule.mem_colon_singleton.mpr (by simpa [smul_eq_mul] using hst)))

end SerreCriterionReduced

open SerreCriterionReduced

/-- **Serre's criterion for reducedness** (Stacks, Tag 031R, Lemma 10.157.3). A Noetherian ring
`R` is reduced if and only if

* `(R₀)`: for every prime `p` of `R` with `p.height = 0`, the localization `R_p` is a regular
  local ring (`IsRegularLocalRing`), and
* `(S₁)`: for every prime `p` of `R`,
  `min 1 (ringKrullDim R_p) ≤ IsLocalRing.depth R_p`, where `R_p` is regarded as a module over
  itself and the inequality is taken in `WithBot ℕ∞`.

Depth is Mathlib's `Ext`-based `IsLocalRing.depth`; for the Noetherian local ring `R_p` it equals
the supremum of the lengths of `R_p`-regular sequences in its maximal ideal
(`IsLocalRing.depth_eq_sSup_length_isRegular`), which is the definition used in the source
(Tag 00LE). The properties `(R₀)` and `(S₁)` are those of Tag 031P. No hypothesis of the printed
statement is dropped. -/
theorem isReduced_iff_forall_isRegularLocalRing_and_min_one_le_depth
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsReduced R ↔
      (∀ (p : Ideal R) [p.IsPrime], p.height = 0 →
        IsRegularLocalRing (Localization.AtPrime p)) ∧
      (∀ (p : Ideal R) [p.IsPrime], min 1 (ringKrullDim (Localization.AtPrime p)) ≤
        ((IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) :
          ℕ∞) : WithBot ℕ∞)) := by
  constructor
  · intro hred
    refine ⟨fun p _ hp ↦ ?_, fun p _ ↦ ?_⟩
    · -- `(R₀)`: `R_p` is a reduced zero-dimensional Noetherian local ring, hence a field.
      have hdim : ringKrullDim (Localization.AtPrime p) = 0 := by
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, hp]; rfl
      have : Ring.KrullDimLE 0 (Localization.AtPrime p) :=
        Ring.krullDimLE_iff.mpr (by rw [hdim]; rfl)
      have : IsArtinianRing (Localization.AtPrime p) :=
        IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
      have hfield := IsArtinianRing.isField_of_isReduced_of_isLocalRing (Localization.AtPrime p)
      rw [isRegularLocalRing_iff, (IsLocalRing.isField_iff_maximalIdeal_eq).mp hfield,
        Submodule.spanFinrank_bot, hdim]
      rfl
    · -- `(S₁)`
      by_cases hp : p.height = 0
      · rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, hp]
        exact (min_le_right _ _).trans (WithBot.coe_le_coe.mpr zero_le)
      · have hmax : (maximalIdeal (Localization.AtPrime p)).height ≠ 0 := by
          intro h0
          apply hp
          have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := Localization.AtPrime p)
          rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, h0] at this
          exact_mod_cast this.symm
        have h1 : (1 : ℕ∞) ≤
            IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) :=
          IsLocalRing.one_le_depth_iff.mpr (exists_isSMulRegular_of_height_ne_zero hmax)
        exact (min_le_left _ _).trans (by exact_mod_cast h1)
  · rintro ⟨hR0, hS1⟩
    refine (isReduced_iff R).mpr fun x hx ↦ ?_
    by_contra hx0
    obtain ⟨P, hP, hxP⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x hx0
    have := hP.toIsPrime
    obtain ⟨y, hy⟩ := hP.eq_radical_colon
    have hyP : (⊥ : Submodule R R).colon {y} ≤ P := hy ▸ Ideal.le_radical
    -- `P` has height zero, by `(S₁)`.
    have hP0 : P.height = 0 := by
      by_contra hne
      have hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime P) := by
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height P]
        exact_mod_cast Order.one_le_iff_ne_zero.mpr hne
      have h1 : (1 : ℕ∞) ≤
          IsLocalRing.depth (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) := by
        have := (le_min le_rfl hdim).trans (hS1 P)
        exact_mod_cast this
      obtain ⟨z, hz, hzreg⟩ := IsLocalRing.one_le_depth_iff.mp h1
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl z
      have ha : a ∈ P := (IsLocalization.AtPrime.mk'_mem_maximal_iff _ P a s).mp hz
      have hareg : IsSMulRegular (Localization.AtPrime P)
          (algebraMap R (Localization.AtPrime P) a) := by
        rw [← IsLocalization.mk'_spec (Localization.AtPrime P) a s]
        exact hzreg.mul ((IsLocalization.map_units (Localization.AtPrime P) s).isSMulRegular _)
      rw [hy] at ha
      obtain ⟨n, hn⟩ := ha
      have hny : a ^ n * y = 0 := by
        simpa [smul_eq_mul] using Submodule.mem_colon_singleton.mp hn
      have h2 : IsSMulRegular (Localization.AtPrime P)
          ((algebraMap R (Localization.AtPrime P) a) ^ n) := hareg.pow n
      apply algebraMap_ne_zero_of_colon_le hyP
      apply h2
      simp only [smul_eq_mul, mul_zero, ← map_pow, ← map_mul, hny, map_zero]
    -- `R_P` is regular local, hence a domain, so `x` vanishes in `R_P`.
    have := hR0 P hP0
    have := IsRegularLocalRing.isDomain (Localization.AtPrime P)
    apply algebraMap_ne_zero_of_colon_le hxP
    exact (hx.map (algebraMap R (Localization.AtPrime P))).eq_zero
