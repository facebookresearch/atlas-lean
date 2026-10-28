/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.SystemOfParameters
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.RegularRingFoundation
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.PrimeAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.VariableInductionCM
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.QuotientByRegularIsCM
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMQuotientFull
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Module.SpanRank
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Erase
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# `dim ≤ grade` for Noetherian regular local rings (Matsumura 17.8, grade half)

For a Noetherian local ring `(R, 𝔪)` with `IsRegularLocal R`
(`RegularRingFoundation.lean`, the project predicate
`𝔪.spanFinrank = ringKrullDim R`), `ringKrullDim R ≤ ↑(grade R R 𝔪)`
(`dim_le_grade_of_isRegularLocal`). Combined with the proved reverse
inequality `GradeDepthFragment.grade_le_ringKrullDim`, this closes `grade = dim`
(`grade_eq_dim_of_isRegularLocal`, i.e. `DepthEqDimAt`) for every Noetherian
regular local ring — the Matsumura Theorem 17.8 content
("a regular local ring is CM").

## Literature (all extracted read-only from the Matsumura CRT scan;
theorem numbers match, scan pages differ from the task's edition)

* Th 14.2 (scan book p105): `(x₁..xᵢ)` is part of a regular system of
  parameters ⟺ their images mod `𝔪²` are independent ⟺ `R/(x₁..xᵢ)` is
  regular of dimension `n - i`. Used in the `i = 1`, `(2)=>(3)` case
  (`rungAvoid_quotient_regular`).
* Th 14.3 (scan book p106): a regular local ring is a domain
  (`isDomain_of_isRegularLocalRing`).
* Th 17.8 (scan book p137): a regular local ring is CM, via the chain
  `(x₁) ⊂ (x₁,x₂) ⊂ ⋯` of prime ideals
  (`dim_le_grade_of_isRegularLocal`).
* Th 14.1(i) (dimension drop across one parameter) is subsumed by Mathlib's
  `ringKrullDim_le_ringKrullDim_quotSMulTop_succ` (Stacks 0B52).

## Structure

Bridge (§3.0) → parameters (§3.1, `SystemOfParameters`) → sop-lift → rung →
rung-avoid → L2 = 14.3 (§3.3) → rung induction (§3.4) → grade assembly
(§3.5), plus the independent side-condition C1 (`dim_atPrime_lt_top`, §4
Route A). Lemma order is acyclic: sop-lift uses only dimension API;
rung adds sop-lift; rung-avoid adds rung; L2 uses rung-avoid + IH on
smaller dimension; the assembly uses rung + L2 per rung.

## Deviations from the design note (all by citation, in the C2-subsumption spirit)

* Sop-exist (s.o.p. from scratch) is bypassed: sop-lift
  (`dim_quot_le_succ_of_mem_maximal`) cites Mathlib's Stacks-0B52 inequality
  directly instead of rebuilding it from hdt.
* Rung-avoid avoids the design note's unpinned Nakayama cotangent-lift: a
  unit-coefficient elimination (some parameter-coefficient of `x` is a unit,
  else `x ∈ 𝔪²`) drops one generator of the quotient maximal ideal.
* L2's completion uses `Ideal.exists_minimalPrimes_le` (one citation) in
  place of the design note's reconstructed nilradical trick.
* The rung assembly uses `isWeaklyRegular_append_iff` + singleton + the
  local `of_isWeaklyRegular_of_mem_maximalIdeal` instead of cons-assembly
  with manual properness.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace DimLeGradeRegular

open RingTheory.Sequence IsLocalRing
open scoped Pointwise

/-! ## §0 Prefix-list helpers -/

/-- `ofList` of a successor-prefix splits as the prefix plus the next element.
List side is `List.take_add_one` (`List.take_succ` is deprecated in this
toolchain); ideal side is `ofList_append` / `ofList_singleton`. -/
theorem ofList_take_succ (R : Type*) [CommRing R] (rs : List R) (i : ℕ)
    (hi : i < rs.length) :
    Ideal.ofList (rs.take (i + 1)) =
      Ideal.ofList (rs.take i) ⊔ Ideal.span {rs[i]} := by
  have htake : rs.take (i + 1) = rs.take i ++ [rs[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]
    rfl
  rw [htake, Ideal.ofList_append, Ideal.ofList_singleton]

#print axioms ofList_take_succ

/-- Prefix ideals sit below the maximal ideal when the full list spans it. -/
theorem ofList_take_le_maximal (R : Type*) [CommRing R] [IsLocalRing R]
    (rs : List R) (hspan : Ideal.ofList rs = maximalIdeal R) (i : ℕ) :
    Ideal.ofList (rs.take i) ≤ maximalIdeal R := by
  rw [← hspan]
  apply Submodule.span_mono
  intro r hr
  exact List.mem_of_mem_take hr

#print axioms ofList_take_le_maximal

/-- Elements of the parameter list lie in the maximal ideal. -/
theorem mem_maximal_of_mem_rs (R : Type*) [CommRing R] [IsLocalRing R]
    (rs : List R) (hspan : Ideal.ofList rs = maximalIdeal R) {r : R}
    (hr : r ∈ rs) : r ∈ maximalIdeal R := by
  rw [← hspan]
  exact Ideal.subset_span hr

#print axioms mem_maximal_of_mem_rs

/-- Cast injectivity for dimension equations stated with single `ℕ` casts. -/
theorem nat_eq_of_dim_eq {a b : ℕ}
    (h : (a : WithBot ℕ∞) = (b : WithBot ℕ∞)) : a = b := by
  exact_mod_cast h

#print axioms nat_eq_of_dim_eq

/-! ## §1 Bridge: predicate ↔ class (design note §3.0) -/

/-- Bridge (design note §3.0): the project predicate `IsRegularLocal` unfolds to
Mathlib's class `IsRegularLocalRing`. -/
theorem regularClass_of_isRegularLocal (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : IsRegularLocal R) : IsRegularLocalRing R :=
  (isRegularLocal_iff_isRegularLocalRing R).mp h

#print axioms regularClass_of_isRegularLocal

/-! ## C1: `ringKrullDim R_Q < ⊤` (design note §4, independent) -/

/-- C1 (design note §4, Route A): finiteness of `dim R_Q` via the in-tree
`dim ≤ ↑embdim` bound. Verbatim copy of the `hfinRQ` precedent
(`SelectedPathDepth.lean`). -/
theorem dim_atPrime_lt_top (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    ringKrullDim (Localization.AtPrime Q) < ⊤ :=
  lt_of_le_of_lt
    (CMQuotientFull.dim_atPrime_le_spanFinrank m K Q)
    (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))

#print axioms dim_atPrime_lt_top

/-! ## §2 Rung engine I: sop-lift and rung (design note §3.2) -/

/-- Sop-lift (design note §3.2, the Matsumura Th 14.1(i) argument): quotient by an
element of the maximal ideal drops dimension by at most one. Proved by
citation (the design note's sop-exist s.o.p. construction is bypassed): Mathlib's
`ringKrullDim_le_ringKrullDim_quotSMulTop_succ` (Stacks 0B52, "the second
inequality") gives the bound for the point-quotient `R ⧸ x • ⊤`,
transported across `x • ⊤ = span {x}` (the exact bridge used at
`KrullDimension/Regular.lean`). Needs only `x ∈ 𝔪`. -/
theorem dim_quot_le_succ_of_mem_maximal (S : Type*) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] {x : S} (hx : x ∈ maximalIdeal S) :
    ringKrullDim S ≤ ringKrullDim (S ⧸ Ideal.span {x}) + 1 := by
  have hbridge : Ideal.span {x} = x • (⊤ : Ideal S) := by
    simp [← Submodule.ideal_span_singleton_smul]
  have heq := ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hbridge.symm)
  have hle := ringKrullDim_le_ringKrullDim_quotSMulTop_succ (R := S) hx
  rwa [heq] at hle

#print axioms dim_quot_le_succ_of_mem_maximal

/-- Rung (design note §3.2, Matsumura Th 14.2 `(2)=>(3)` for `i = 1`, dimension
half): a Noetherian local ring that is regular of dimension `d + 1` stays
regular of dimension `d` after quotienting by `x ∈ 𝔪`, provided the
quotient maximal ideal is spanned by `≤ d` elements (no `𝔪/𝔪²` argument is
needed at this step). Lower bound by sop-lift; upper bound by Krull's hdt
plus the spanning hypothesis; regularity by
`IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`. -/
theorem rung_quotient_regular_of_spanning (S : Type*) [CommRing S]
    [IsRegularLocalRing S] {d : ℕ}
    (hdim : ((d + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim S)
    {x : S} (hx : x ∈ maximalIdeal S)
    [IsLocalRing (S ⧸ Ideal.span {x})]
    {s : Finset (S ⧸ Ideal.span {x})}
    (hspan : Ideal.span (↑s : Set (S ⧸ Ideal.span {x})) =
      maximalIdeal (S ⧸ Ideal.span {x}))
    (hcard : s.card ≤ d) :
    IsRegularLocalRing (S ⧸ Ideal.span {x}) ∧
      ringKrullDim (S ⧸ Ideal.span {x}) = (d : WithBot ℕ∞) := by
  have hemb : (maximalIdeal (S ⧸ Ideal.span {x})).spanFinrank ≤ d := by
    have hfin : ((↑s : Set (S ⧸ Ideal.span {x}))).Finite :=
      Finset.finite_toSet s
    have hle := Submodule.spanFinrank_span_le_ncard_of_finite
      (R := S ⧸ Ideal.span {x}) hfin
    have hspan' : Submodule.span (S ⧸ Ideal.span {x})
        (↑s : Set (S ⧸ Ideal.span {x})) =
        maximalIdeal (S ⧸ Ideal.span {x}) := hspan
    rw [hspan', Set.ncard_coe_finset] at hle
    exact hle.trans hcard
  have hHDT := ringKrullDim_le_spanFinrank_maximalIdeal (S ⧸ Ideal.span {x})
  have hub : ringKrullDim (S ⧸ Ideal.span {x}) ≤ (d : WithBot ℕ∞) := by
    refine hHDT.trans ?_
    exact_mod_cast hemb
  have hle := dim_quot_le_succ_of_mem_maximal S hx
  rw [← hdim] at hle
  have hQne : ringKrullDim (S ⧸ Ideal.span {x}) ≠ ⊥ := by
    intro hcon
    rw [hcon] at hle
    have h1 : (⊥ : WithBot ℕ∞) + 1 = ⊥ := rfl
    rw [h1] at hle
    have h2 : ((d + 1 : ℕ) : WithBot ℕ∞) = ⊥ := le_bot_iff.mp hle
    exact WithBot.coe_ne_bot h2
  obtain ⟨k, hk⟩ := WithBot.ne_bot_iff_exists.mp hQne
  have hklow : (d : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ Ideal.span {x}) := by
    rw [← hk] at hle hub ⊢
    by_cases hkT : k = ⊤
    · subst hkT
      change (d : WithBot ℕ∞) ≤ ⊤
      exact le_top
    · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hkT
      have hmcast : ((m : ℕ) : ℕ∞) = k := hm
      subst hmcast
      have h2 : d + 1 ≤ m + 1 := by exact_mod_cast hle
      have h4 : d ≤ m := by omega
      have h5 : (((d : ℕ∞)) : WithBot ℕ∞) ≤ (((m : ℕ∞)) : WithBot ℕ∞) := by
        exact_mod_cast h4
      rw [WithBot.coe_natCast]
      rwa [WithBot.coe_natCast, WithBot.coe_natCast] at h5
  have hdimQ : ringKrullDim (S ⧸ Ideal.span {x}) = (d : WithBot ℕ∞) :=
    le_antisymm hub hklow
  have hregQ : IsRegularLocalRing (S ⧸ Ideal.span {x}) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
      (S ⧸ Ideal.span {x}) (by
        rw [hdimQ]
        exact_mod_cast hemb)
  exact ⟨hregQ, hdimQ⟩

#print axioms rung_quotient_regular_of_spanning

/-- Rung-avoid (design note §3.2, Matsumura Th 14.2 `(2)=>(3)` for `i = 1`):
quotient of a regular local ring of dimension `d + 1` by `x ∈ 𝔪 ∖ 𝔪²`
is regular of dimension `d`. Proof by unit-coefficient elimination
(deviation from the design note's cotangent-basis Nakayama lift, whose key lemma
is unpinned in Mathlib): write `x` in the parameter generators; some
coefficient is a unit (else `x ∈ 𝔪²`); solve for that generator and drop
it, leaving `d` generators of the quotient maximal ideal; close by rung. -/
theorem rungAvoid_quotient_regular (S : Type*) [CommRing S]
    [IsRegularLocalRing S] {d : ℕ}
    (hdim : ((d + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim S)
    {x : S} (hx : x ∈ maximalIdeal S)
    (hx2 : x ∉ maximalIdeal S ^ 2) :
    IsRegularLocalRing (S ⧸ Ideal.span {x}) ∧
      ringKrullDim (S ⧸ Ideal.span {x}) = (d : WithBot ℕ∞) := by
  classical
  obtain ⟨rs, hspan, hlen, hdimrs⟩ :=
    SystemOfParameters.exists_list_ofList_maximalIdeal S
  have hlenD : rs.length = d + 1 := by
    have h1 : ((rs.length : ℕ) : WithBot ℕ∞) =
        ((d + 1 : ℕ) : WithBot ℕ∞) := by
      rw [hdimrs, hdim]
    exact nat_eq_of_dim_eq h1
  have hxle : Ideal.span {x} ≤ maximalIdeal S :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  have hlocQ : IsLocalRing (S ⧸ Ideal.span {x}) :=
    QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal _ hxle
  have hmaxmap := QuotientByRegularIsCM.maximalIdeal_quotient_eq_map
    (Ideal.span {x}) hxle
  have hmem : ∀ r ∈ rs, r ∈ maximalIdeal S :=
    fun r hr => mem_maximal_of_mem_rs S rs hspan hr
  have hset : { r | r ∈ rs } = (↑(rs.toFinset) : Set S) := by
    ext r
    simp
  have hxspan : x ∈ Submodule.span S (↑(rs.toFinset) : Set S) := by
    have h1 : x ∈ Ideal.ofList rs := by
      rw [hspan]
      exact hx
    have h1' : x ∈ Ideal.span {r | r ∈ rs} := h1
    rw [hset] at h1'
    exact h1'
  obtain ⟨f, hsupp, hsum⟩ := Submodule.mem_span_finset.mp hxspan
  obtain ⟨a₀, ha₀mem, ha₀unit⟩ : ∃ a₀ ∈ rs.toFinset, IsUnit (f a₀) := by
    by_contra hcon
    push Not at hcon
    have hmem' : ∀ a₀ ∈ rs.toFinset, f a₀ ∈ maximalIdeal S := by
      intro a₀ ha₀
      have hni : ¬IsUnit (f a₀) := hcon a₀ ha₀
      rw [mem_maximalIdeal, mem_nonunits_iff]
      exact hni
    apply hx2
    have hpow : x ∈ maximalIdeal S * maximalIdeal S := by
      rw [← hsum]
      apply Submodule.sum_mem
      intro a ha
      have hfa : f a ∈ maximalIdeal S := hmem' a ha
      have ham : a ∈ maximalIdeal S := hmem a (List.mem_toFinset.mp ha)
      rw [smul_eq_mul]
      exact Ideal.mul_mem_mul hfa ham
    rwa [pow_two]
  obtain ⟨b, hb1, hb2⟩ := isUnit_iff_exists.mp ha₀unit
  have hπx : Ideal.Quotient.mk (Ideal.span {x}) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hsplit := Finset.add_sum_erase (rs.toFinset) (fun a => f a • a) ha₀mem
  have hmap : Ideal.Quotient.mk (Ideal.span {x}) (f a₀ • a₀) +
      Ideal.Quotient.mk (Ideal.span {x})
        (∑ a ∈ (rs.toFinset).erase a₀, f a • a) = 0 := by
    have h := congrArg (Ideal.Quotient.mk (Ideal.span {x}))
      (hsplit.trans hsum)
    rwa [map_add, hπx] at h
  have hsumQ : Ideal.Quotient.mk (Ideal.span {x})
        (∑ a ∈ (rs.toFinset).erase a₀, f a • a) =
        ∑ a ∈ (rs.toFinset).erase a₀,
          (Ideal.Quotient.mk (Ideal.span {x}) (f a)) *
          (Ideal.Quotient.mk (Ideal.span {x}) a) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [smul_eq_mul, map_mul]
  have hsol : Ideal.Quotient.mk (Ideal.span {x}) a₀ =
      -∑ a ∈ (rs.toFinset).erase a₀,
        ((Ideal.Quotient.mk (Ideal.span {x}) b *
          Ideal.Quotient.mk (Ideal.span {x}) (f a))) *
        (Ideal.Quotient.mk (Ideal.span {x}) a) := by
    have h1 : Ideal.Quotient.mk (Ideal.span {x}) (f a₀ • a₀) =
        Ideal.Quotient.mk (Ideal.span {x}) (f a₀) *
          Ideal.Quotient.mk (Ideal.span {x}) a₀ := by
      rw [smul_eq_mul, map_mul]
    rw [h1, hsumQ] at hmap
    have hb : Ideal.Quotient.mk (Ideal.span {x}) b *
        Ideal.Quotient.mk (Ideal.span {x}) (f a₀) = 1 := by
      rw [← map_mul, hb2, map_one]
    have h2 := congrArg (Ideal.Quotient.mk (Ideal.span {x}) b * ·) hmap
    rw [mul_add, mul_zero] at h2
    have h3 : Ideal.Quotient.mk (Ideal.span {x}) b *
        (Ideal.Quotient.mk (Ideal.span {x}) (f a₀) *
          Ideal.Quotient.mk (Ideal.span {x}) a₀) =
        Ideal.Quotient.mk (Ideal.span {x}) a₀ := by
      rw [← mul_assoc, hb, one_mul]
    rw [h3] at h2
    have h4 : Ideal.Quotient.mk (Ideal.span {x}) a₀ =
        -(Ideal.Quotient.mk (Ideal.span {x}) b *
          ∑ a ∈ (rs.toFinset).erase a₀,
            (Ideal.Quotient.mk (Ideal.span {x}) (f a)) *
            (Ideal.Quotient.mk (Ideal.span {x}) a)) :=
      eq_neg_of_add_eq_zero_left h2
    rw [h4, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hcard' : (((rs.toFinset).erase a₀).image
      (Ideal.Quotient.mk (Ideal.span {x}))).card ≤ d := by
    have h1 := Finset.card_image_le (s := (rs.toFinset).erase a₀)
      (f := Ideal.Quotient.mk (Ideal.span {x}))
    have h2 : ((rs.toFinset).erase a₀).card = (rs.toFinset).card - 1 :=
      Finset.card_erase_of_mem ha₀mem
    have h3 : (rs.toFinset).card ≤ d + 1 :=
      le_trans (List.toFinset_card_le rs) (le_of_eq hlenD)
    omega
  have hredundant : Ideal.Quotient.mk (Ideal.span {x}) a₀ ∈ Ideal.span
      (↑(((rs.toFinset).erase a₀).image
        (Ideal.Quotient.mk (Ideal.span {x}))) :
        Set (S ⧸ Ideal.span {x})) := by
    rw [hsol]
    apply Submodule.neg_mem
    apply Submodule.sum_mem
    intro a ha
    have hπmem : Ideal.Quotient.mk (Ideal.span {x}) a ∈
        ((rs.toFinset).erase a₀).image (Ideal.Quotient.mk (Ideal.span {x})) :=
      Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hspanmem : Ideal.Quotient.mk (Ideal.span {x}) a ∈ Ideal.span
        (↑(((rs.toFinset).erase a₀).image
          (Ideal.Quotient.mk (Ideal.span {x}))) :
          Set (S ⧸ Ideal.span {x})) :=
      Ideal.subset_span (Finset.mem_coe.mpr hπmem)
    rw [← smul_eq_mul]
    exact Submodule.smul_mem _ _ hspanmem
  have hspanQ : Ideal.span (↑(((rs.toFinset).erase a₀).image
        (Ideal.Quotient.mk (Ideal.span {x}))) : Set (S ⧸ Ideal.span {x})) =
      maximalIdeal (S ⧸ Ideal.span {x}) := by
    have hmap : maximalIdeal (S ⧸ Ideal.span {x}) =
        Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span {x}))) := by
      rw [hmaxmap, ← hspan, Ideal.map_ofList]
    rw [hmap]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      have har : a ∈ rs :=
        List.mem_toFinset.mp (Finset.mem_of_mem_erase ha)
      exact Ideal.subset_span (List.mem_map.mpr ⟨a, har, rfl⟩)
    · apply Submodule.span_le.mpr
      intro y hy
      obtain ⟨a, har, rfl⟩ := List.mem_map.mp hy
      by_cases haa : a = a₀
      · subst haa
        exact hredundant
      · have haerase : a ∈ (rs.toFinset).erase a₀ :=
          Finset.mem_erase.mpr ⟨haa, List.mem_toFinset.mpr har⟩
        exact Ideal.subset_span
          (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, haerase, rfl⟩))
  exact rung_quotient_regular_of_spanning S hdim hx hspanQ hcard'

#print axioms rungAvoid_quotient_regular

/-! ## §3 L2: regular local rings are domains (design note §3.3, Th 14.3) -/

/-- L2 induction (design note §3.3, Matsumura Th 14.3 p106): a Noetherian regular
local ring with `𝔪.spanFinrank = k` is a domain, by induction on `k`. The
`k = 0` case is a field; for `k + 1` (uniform, no separate `n = 1` case)
prime avoidance picks `x ∈ 𝔪 ∖ (𝔪² ∪ ⋃ minimalPrimes ⊥)`; `R ⧸ span {x}`
is regular of dimension `k` (rung-avoid) hence a domain by IH, so
`span {x}` is prime; a minimal prime inside it
(`Ideal.exists_minimalPrimes_le`, subsuming the design note's nilradical trick by
citation) satisfies `𝔭 = x𝔭`, hence `𝔭 = ⊥` by Nakayama, so `⊥` is prime.
This auxiliary lemma carries the induction; see
`isDomain_of_isRegularLocalRing` for the clean form. -/
theorem isDomain_of_isRegularLocalRing_aux : ∀ (k : ℕ) (S : Type*)
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S],
    IsRegularLocalRing S → (maximalIdeal S).spanFinrank = k → IsDomain S := by
  intro k
  induction k with
  | zero =>
    intro S _ _ _ hreg hk
    have hfg := Ideal.fg_of_isNoetherianRing (maximalIdeal S)
    have hbot : maximalIdeal S = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp hk
    have hfield : IsField S := isField_iff_maximalIdeal_eq.mpr hbot
    let hF : Field S := hfield.toField
    exact NoZeroDivisors.to_isDomain S
  | succ k ih =>
    intro S _ _ _ hreg hk
    have hregI : IsRegularLocalRing S := hreg
    have hdim : ((k + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim S := by
      have hreg' := (isRegularLocalRing_iff S).mp hreg
      rw [hk] at hreg'
      exact hreg'
    have hfin : ((⊥ : Ideal S).minimalPrimes).Finite :=
      Ideal.finite_minimalPrimes_of_isNoetherianRing S ⊥
    have hp : ∀ i ∈ ({maximalIdeal S ^ 2} ∪ hfin.toFinset),
        i ≠ maximalIdeal S ^ 2 → i ≠ maximalIdeal S ^ 2 → i.IsPrime := by
      intro i hi h1 h2
      rw [Finset.mem_union, Finset.mem_singleton] at hi
      rcases hi with rfl | hi
      · exact (h1 rfl).elim
      · have hiP : i ∈ (⊥ : Ideal S).minimalPrimes := hfin.mem_toFinset.mp hi
        exact Ideal.IsMinimalPrime.isPrime hiP
    have hle : ∀ i ∈ ({maximalIdeal S ^ 2} ∪ hfin.toFinset),
        ¬maximalIdeal S ≤ i := by
      intro i hi
      rw [Finset.mem_union, Finset.mem_singleton] at hi
      rcases hi with rfl | hi
      · intro hle2
        have hfg := Ideal.fg_of_isNoetherianRing (maximalIdeal S)
        have hleS : (maximalIdeal S : Submodule S S) ≤
            maximalIdeal S • (maximalIdeal S : Submodule S S) := by
          have hsub : (maximalIdeal S : Submodule S S) ≤
              ((maximalIdeal S ^ 2 : Ideal S) : Submodule S S) := hle2
          have hsq : ((maximalIdeal S ^ 2 : Ideal S) : Submodule S S) =
              maximalIdeal S • (maximalIdeal S : Submodule S S) := by
            rw [← QuotientByRegularIsCM.smul_top_eq_self (maximalIdeal S ^ 2),
              pow_two, Submodule.mul_smul,
              QuotientByRegularIsCM.smul_top_eq_self]
          rwa [hsq] at hsub
        have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
          (maximalIdeal S) (maximalIdeal S : Submodule S S) hfg hleS
          (maximalIdeal_le_jacobson ⊥)
        have h0 : (maximalIdeal S).spanFinrank = 0 :=
          (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mpr hbot
        rw [hk] at h0
        omega
      · have hiP : i ∈ (⊥ : Ideal S).minimalPrimes := hfin.mem_toFinset.mp hi
        have hPprime : i.IsPrime := Ideal.IsMinimalPrime.isPrime hiP
        intro hleP
        have hPE : maximalIdeal S = i :=
          (maximalIdeal.isMaximal S).eq_of_le hPprime.ne_top hleP
        have hiP' : i ∈ minimalPrimes S := hiP
        have hPh0 : i.height = 0 := Ideal.height_eq_zero_iff.mpr hiP'
        have hht : (maximalIdeal S).height = 0 := by
          rw [hPE]
          exact hPh0
        have hdimht : ((((maximalIdeal S).height : ℕ∞)) : WithBot ℕ∞) =
            ringKrullDim S :=
          maximalIdeal_height_eq_ringKrullDim (R := S)
        rw [hht] at hdimht
        have z : (((0 : ℕ∞)) : WithBot ℕ∞) = ((0 : ℕ) : WithBot ℕ∞) := by
          rw [← WithBot.coe_natCast, Nat.cast_zero]
        rw [z] at hdimht
        have e4 : (0 : ℕ) = k + 1 := nat_eq_of_dim_eq (hdimht.trans hdim.symm)
        omega
    obtain ⟨x, hxmem, hxavoid⟩ :=
      PrimeAvoidance.exists_mem_notMem_of_forall_not_le
        (s := {maximalIdeal S ^ 2} ∪ hfin.toFinset) (f := id)
        (maximalIdeal S ^ 2) (maximalIdeal S ^ 2) hp (maximalIdeal S) hle
    have hx2 : x ∉ maximalIdeal S ^ 2 := hxavoid _ (by simp)
    have hxavoidP : ∀ P ∈ (⊥ : Ideal S).minimalPrimes, x ∉ P := by
      intro P hP
      have hmem : P ∈ ({maximalIdeal S ^ 2} ∪ hfin.toFinset) :=
        Finset.mem_union.mpr (Or.inr (hfin.mem_toFinset.mpr hP))
      exact hxavoid P hmem
    have hxle : Ideal.span {x} ≤ maximalIdeal S :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxmem)
    have hlocQ : IsLocalRing (S ⧸ Ideal.span {x}) :=
      QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal _ hxle
    obtain ⟨hregQ, hdimQ⟩ :=
      rungAvoid_quotient_regular S (d := k) hdim hxmem hx2
    have hregQI : IsRegularLocalRing (S ⧸ Ideal.span {x}) := hregQ
    have hkQ : (maximalIdeal (S ⧸ Ideal.span {x})).spanFinrank = k := by
      have e := (isRegularLocalRing_iff (S ⧸ Ideal.span {x})).mp hregQ
      rw [hdimQ] at e
      exact nat_eq_of_dim_eq e
    have hdomQ : IsDomain (S ⧸ Ideal.span {x}) :=
      ih (S ⧸ Ideal.span {x}) hregQ hkQ
    have hprime : (Ideal.span {x}).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp hdomQ
    obtain ⟨P, hPmin, hPle⟩ := Ideal.exists_minimalPrimes_le
      (I := (⊥ : Ideal S)) (J := Ideal.span {x}) bot_le
    have hPprime : P.IsPrime := Ideal.IsMinimalPrime.isPrime hPmin
    have hxP : x ∉ P := hxavoidP P hPmin
    have hsub : (P : Submodule S S) ≤
        Ideal.span {x} • (P : Submodule S S) := by
      intro y hy
      have hyx : y ∈ Ideal.span {x} := hPle hy
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hyx
      have hxa : x * a ∈ P := by
        rw [mul_comm, ha]
        exact hy
      have haP : a ∈ P := (hPprime.mem_or_mem hxa).resolve_left hxP
      have hmem : x • a ∈ Ideal.span {x} • (P : Submodule S S) :=
        Submodule.smul_mem_smul (Ideal.subset_span (by simp)) haP
      have hya : y = x • a := by
        rw [smul_eq_mul, mul_comm]
        exact ha.symm
      rwa [hya]
    have hPbot : (P : Submodule S S) = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x})
        (P : Submodule S S) (Ideal.fg_of_isNoetherianRing P) hsub
        (le_trans hxle (maximalIdeal_le_jacobson ⊥))
    have hPeq : P = ⊥ := hPbot
    rw [hPeq] at hPprime
    have hNZD : NoZeroDivisors S := ⟨fun {a b} hmul => by
      have hmem : a * b ∈ (⊥ : Ideal S) := by
        rw [hmul]
        exact Submodule.zero_mem ⊥
      have hor := hPprime.mem_or_mem hmem
      rcases hor with ha | hb
      · exact Or.inl ((Submodule.mem_bot S).mp ha)
      · exact Or.inr ((Submodule.mem_bot S).mp hb)⟩
    exact NoZeroDivisors.to_isDomain S

#print axioms isDomain_of_isRegularLocalRing_aux

/-- L2 clean form (Matsumura Th 14.3): every Noetherian regular local ring
is a domain. -/
theorem isDomain_of_isRegularLocalRing (S : Type*) [CommRing S]
    [IsRegularLocalRing S] : IsDomain S :=
  isDomain_of_isRegularLocalRing_aux (maximalIdeal S).spanFinrank S
    inferInstance rfl

#print axioms isDomain_of_isRegularLocalRing

/-! ## §4 Rung assembly (design note §3.4, Matsumura Th 17.8) -/

/-- Elements survive in the drop: `rs[i] ∈ drop i rs`. Via
`List.getElem_drop` (`(drop i rs)[0] = rs[i + 0]`) and `List.getElem_mem`. -/
theorem getElem_mem_drop (α : Type*) (rs : List α) (i : ℕ)
    (hi : i < rs.length) : rs[i] ∈ rs.drop i := by
  have h0len : 0 < (rs.drop i).length := by
    rw [List.length_drop]
    omega
  have e1 : (rs.drop i)[0] = rs[i] := List.getElem_drop (h := h0len)
  exact e1 ▸ (List.getElem_mem h0len)

#print axioms getElem_mem_drop

/-- A zero head contributes nothing to `ofList`. -/
theorem ofList_cons_zero (R : Type*) [CommRing R] (rs : List R) :
    Ideal.ofList (0 :: rs) = Ideal.ofList rs := by
  have h0 : Ideal.span ({0} : Set R) = ⊥ :=
    Submodule.span_eq_bot.mpr (by simp)
  rw [Ideal.ofList_cons, h0, bot_sup_eq]

#print axioms ofList_cons_zero

/-- (b) (design note §3.4): the rung maximal ideal is spanned by the drop-images.
`𝔪ᵢ = map mkᵢ 𝔪` (C2) `= ofList (map mkᵢ rs)` (`map_ofList`)
`= ofList (map mkᵢ (drop i rs))` (take-images vanish). Proved directly per
rung (no induction): the take part maps to zero. -/
theorem maximalIdeal_rung_eq_ofList_drop (R : Type*) [CommRing R]
    [IsLocalRing R] (rs : List R)
    (hspan : Ideal.ofList rs = maximalIdeal R) (i : ℕ)
    [IsLocalRing (R ⧸ Ideal.ofList (rs.take i))] :
    maximalIdeal (R ⧸ Ideal.ofList (rs.take i)) =
      Ideal.ofList
        ((rs.drop i).map (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))) := by
  have hle : Ideal.ofList (rs.take i) ≤ maximalIdeal R :=
    ofList_take_le_maximal R rs hspan i
  have key : (rs.take i).map (Ideal.Quotient.mk (Ideal.ofList (rs.take i))) ++
      (rs.drop i).map (Ideal.Quotient.mk (Ideal.ofList (rs.take i))) =
      rs.map (Ideal.Quotient.mk (Ideal.ofList (rs.take i))) := by
    rw [← List.map_append, List.take_append_drop]
  have hvan : Ideal.ofList
      ((rs.take i).map (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))) = ⊥ := by
    apply Submodule.span_eq_bot.mpr
    intro y hy
    simp only [Set.mem_ofPred_eq] at hy
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hr)
  rw [QuotientByRegularIsCM.maximalIdeal_quotient_eq_map _ hle, ← hspan,
    Ideal.map_ofList, ← key, Ideal.ofList_append, hvan]
  exact bot_sup_eq _

#print axioms maximalIdeal_rung_eq_ofList_drop

/-- Embedding-dimension bound per rung: from (b), `𝔪ᵢ` is spanned by the
`(drop i).length` drop-images. Used at every rung (base, step, and the
rung spanning input). -/
theorem spanFinrank_rung_le (R : Type*) [CommRing R] [IsLocalRing R]
    (rs : List R) (hspan : Ideal.ofList rs = maximalIdeal R) (i : ℕ)
    [IsLocalRing (R ⧸ Ideal.ofList (rs.take i))] :
    (maximalIdeal (R ⧸ Ideal.ofList (rs.take i))).spanFinrank ≤
      (rs.drop i).length := by
  classical
  have hb := maximalIdeal_rung_eq_ofList_drop R rs hspan i
  have hfin : (↑(((rs.drop i).map
      (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))).toFinset) :
      Set (R ⧸ Ideal.ofList (rs.take i))).Finite :=
    Finset.finite_toSet _
  have hle := Submodule.spanFinrank_span_le_ncard_of_finite
    (R := R ⧸ Ideal.ofList (rs.take i)) hfin
  have hset : (↑(((rs.drop i).map
      (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))).toFinset) :
      Set (R ⧸ Ideal.ofList (rs.take i))) =
      {x | x ∈ (rs.drop i).map
        (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))} := by
    ext x
    simp
  have hspan' : Submodule.span (R ⧸ Ideal.ofList (rs.take i))
      (↑(((rs.drop i).map
        (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))).toFinset) :
        Set (R ⧸ Ideal.ofList (rs.take i))) =
      maximalIdeal (R ⧸ Ideal.ofList (rs.take i)) := by
    rw [hset]
    exact hb.symm
  rw [hspan', Set.ncard_coe_finset] at hle
  have hcard : (((rs.drop i).map
      (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))).toFinset).card ≤
      (rs.drop i).length := by
    have h1 := List.toFinset_card_le ((rs.drop i).map
      (Ideal.Quotient.mk (Ideal.ofList (rs.take i))))
    rwa [List.length_map] at h1
  exact hle.trans hcard

#print axioms spanFinrank_rung_le

/-- (a) (design note §3.4): every rung `Rᵢ = R ⧸ ofList (take i rs)` is regular
of dimension `rs.length - i`. Base `i = 0` is `R ⧸ ⊥ ≃ R`
(`quotientBot`); the step applies rung to `Rᵢ` (spanning from (b) with
the head image killed by `ofList_cons_zero`) and transports the
dimension across `quotQuotEquivQuotSup`. Regularity is via
`of_spanFinrank_maximalIdeal_le` from (b)-spanning + the dim equation
(no backward class transport across the equivs). -/
theorem rung_regular_dim (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (rs : List R) (hspan : Ideal.ofList rs = maximalIdeal R)
    (hdim : ((rs.length : ℕ) : WithBot ℕ∞) = ringKrullDim R)
    (i : ℕ) (hi : i ≤ rs.length) :
    IsRegularLocalRing (R ⧸ Ideal.ofList (rs.take i)) ∧
      ringKrullDim (R ⧸ Ideal.ofList (rs.take i)) =
        ((rs.length - i : ℕ) : WithBot ℕ∞) := by
  revert hi
  induction i with
  | zero =>
    intro _
    rw [Nat.sub_zero]
    have ht0 : Ideal.ofList (rs.take 0) = ⊥ := by
      rw [List.take_zero, Ideal.ofList_nil]
    have hloc0 : IsLocalRing (R ⧸ Ideal.ofList (rs.take 0)) :=
      QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal _
        (ofList_take_le_maximal R rs hspan 0)
    have hdim0 : ringKrullDim (R ⧸ Ideal.ofList (rs.take 0)) =
        ((rs.length : ℕ) : WithBot ℕ∞) := by
      have he := ringKrullDim_eq_of_ringEquiv
        ((Ideal.quotEquivOfEq ht0).trans (RingEquiv.quotientBot R))
      rw [he]
      exact hdim.symm
    have hemb0 : (maximalIdeal (R ⧸ Ideal.ofList (rs.take 0))).spanFinrank ≤
        rs.length := by
      have h := spanFinrank_rung_le R rs hspan 0
      rwa [List.length_drop, Nat.sub_zero] at h
    have hreg0 : IsRegularLocalRing (R ⧸ Ideal.ofList (rs.take 0)) :=
      IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (by
        rw [hdim0]
        exact_mod_cast hemb0)
    exact ⟨hreg0, hdim0⟩
  | succ i IH =>
    intro hi1
    classical
    have hi : i ≤ rs.length := by omega
    have hilt : i < rs.length := by omega
    obtain ⟨hregi, hdimi⟩ := IH hi
    set d := rs.length - (i + 1) with hd
    have hid : rs.length - i = d + 1 := by omega
    have hregI : IsRegularLocalRing (R ⧸ Ideal.ofList (rs.take i)) := hregi
    have hxmem : Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i] ∈
        maximalIdeal (R ⧸ Ideal.ofList (rs.take i)) := by
      have hb := maximalIdeal_rung_eq_ofList_drop R rs hspan i
      rw [hb]
      apply Ideal.subset_span
      exact List.mem_map.mpr ⟨rs[i], getElem_mem_drop _ rs i hilt, rfl⟩
    have hQle : Ideal.span
          {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]} ≤
        maximalIdeal (R ⧸ Ideal.ofList (rs.take i)) :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxmem)
    have hlocQ : IsLocalRing ((R ⧸ Ideal.ofList (rs.take i)) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]}) :=
      QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal _ hQle
    have hdropcons : rs.drop i = rs[i] :: rs.drop (i + 1) := by
      have h1 := List.take_append_drop i rs
      have h2 := List.take_append_drop (i + 1) rs
      have htake : rs.take (i + 1) = rs.take i ++ [rs[i]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hilt]
        rfl
      have h3 := h1.trans h2.symm
      rw [htake, List.append_assoc] at h3
      have h4 := List.append_cancel_left h3
      exact h4
    have hspanQ : Ideal.span (↑(((((rs.drop (i + 1)).map
        (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))).map
        (Ideal.Quotient.mk (Ideal.span
          {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]})))).toFinset) :
        Set ((R ⧸ Ideal.ofList (rs.take i)) ⧸ Ideal.span
          {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]})) =
        maximalIdeal ((R ⧸ Ideal.ofList (rs.take i)) ⧸ Ideal.span
          {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]}) := by
      have hmapQ : maximalIdeal ((R ⧸ Ideal.ofList (rs.take i)) ⧸
            Ideal.span {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]}) =
          Ideal.map (Ideal.Quotient.mk (Ideal.span
            {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]}))
            (maximalIdeal (R ⧸ Ideal.ofList (rs.take i))) :=
        QuotientByRegularIsCM.maximalIdeal_quotient_eq_map _ hQle
      have hb := maximalIdeal_rung_eq_ofList_drop R rs hspan i
      have hmapofList : Ideal.map (Ideal.Quotient.mk (Ideal.span
            {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]}))
            (Ideal.ofList ((rs.drop i).map
              (Ideal.Quotient.mk (Ideal.ofList (rs.take i))))) =
          Ideal.ofList ((((rs.drop i).map
            (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))).map
            (Ideal.Quotient.mk (Ideal.span
              {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]})))) :=
        Ideal.map_ofList _ _
      have hx0 : Ideal.Quotient.mk (Ideal.span
          {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]})
          (Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
      have hhead : ((((rs.drop i).map
          (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))).map
          (Ideal.Quotient.mk (Ideal.span
            {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]})))) =
          0 :: ((((rs.drop (i + 1)).map
            (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))).map
            (Ideal.Quotient.mk (Ideal.span
              {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]})))) := by
        rw [hdropcons, List.map_cons, List.map_cons, hx0]
      have hset : (↑(((((rs.drop (i + 1)).map
          (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))).map
          (Ideal.Quotient.mk (Ideal.span
            {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]})))).toFinset) :
          Set ((R ⧸ Ideal.ofList (rs.take i)) ⧸ Ideal.span
            {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]})) =
          {x : ((R ⧸ Ideal.ofList (rs.take i)) ⧸ Ideal.span
            {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]}) |
            x ∈ ((((rs.drop (i + 1)).map
            (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))).map
            (Ideal.Quotient.mk (Ideal.span
              {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]}))))} := by
        ext x
        simp
      rw [hmapQ, hb, hmapofList, hhead, ofList_cons_zero, hset]
    have hlen : ((((rs.drop (i + 1)).map
        (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))).map
        (Ideal.Quotient.mk (Ideal.span
          {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]})))).length = d := by
      rw [List.length_map, List.length_map, List.length_drop, ← hd]
    have hcardQ : (((((rs.drop (i + 1)).map
        (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))).map
        (Ideal.Quotient.mk (Ideal.span
          {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]})))).toFinset).card ≤ d := by
      have h1 := List.toFinset_card_le ((((rs.drop (i + 1)).map
        (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))).map
        (Ideal.Quotient.mk (Ideal.span
          {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]}))))
      rw [hlen] at h1
      exact h1
    have hdim' : ((d + 1 : ℕ) : WithBot ℕ∞) =
        ringKrullDim (R ⧸ Ideal.ofList (rs.take i)) := by
      rw [← hid, hdimi]
    obtain ⟨hregQ, hdimQ⟩ := rung_quotient_regular_of_spanning
      (R ⧸ Ideal.ofList (rs.take i)) hdim' hxmem hspanQ hcardQ
    have hts : Ideal.ofList (rs.take (i + 1)) =
        Ideal.ofList (rs.take i) ⊔ Ideal.span {rs[i]} :=
      ofList_take_succ R rs i hilt
    have hmapbridge : Ideal.map (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))
        (Ideal.span {rs[i]}) =
        Ideal.span {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]} := by
      rw [Ideal.map_span, Set.image_singleton]
    have he : (R ⧸ Ideal.ofList (rs.take (i + 1))) ≃+*
        ((R ⧸ Ideal.ofList (rs.take i)) ⧸ Ideal.span
          {Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i]}) :=
      (Ideal.quotEquivOfEq hts).trans
        ((DoubleQuot.quotQuotEquivQuotSup (Ideal.ofList (rs.take i))
          (Ideal.span {rs[i]})).symm.trans
          (Ideal.quotEquivOfEq hmapbridge))
    have hdimS : ringKrullDim (R ⧸ Ideal.ofList (rs.take (i + 1))) =
        ((d : ℕ) : WithBot ℕ∞) := by
      have he' := ringKrullDim_eq_of_ringEquiv he
      rw [he', hdimQ]
    have hlocS : IsLocalRing (R ⧸ Ideal.ofList (rs.take (i + 1))) :=
      QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal _
        (ofList_take_le_maximal R rs hspan (i + 1))
    have hembS : (maximalIdeal
        (R ⧸ Ideal.ofList (rs.take (i + 1)))).spanFinrank ≤ d := by
      have h := spanFinrank_rung_le R rs hspan (i + 1)
      rwa [List.length_drop, ← hd] at h
    have hregS : IsRegularLocalRing (R ⧸ Ideal.ofList (rs.take (i + 1))) :=
      IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (by
        rw [hdimS]
        exact_mod_cast hembS)
    exact ⟨hregS, hdimS⟩

#print axioms rung_regular_dim

/-- (c) (design note §3.4): the take-prefixes are weakly regular. Step extends by
`isWeaklyRegular_append_iff` + singleton; the per-rung
`IsSMulRegular` transfers from the rung domain ((a) + L2) across
`quotEquivOfEq` (`J • ⊤ = J`), using dimension-count nonvanishing
(`x̄ = 0` would collapse `Rᵢ₊₁ ≃ Rᵢ`, contradicting the dim drop). -/
theorem rung_weaklyRegular (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (rs : List R) (hspan : Ideal.ofList rs = maximalIdeal R)
    (hdim : ((rs.length : ℕ) : WithBot ℕ∞) = ringKrullDim R)
    (i : ℕ) (hi : i ≤ rs.length) :
    IsWeaklyRegular R (rs.take i) := by
  revert hi
  induction i with
  | zero =>
    intro _
    rw [List.take_zero]
    exact IsWeaklyRegular.nil R R
  | succ i IH =>
    intro hi1
    have hi : i ≤ rs.length := by omega
    have hilt : i < rs.length := by omega
    obtain ⟨hregi, hdimi⟩ := rung_regular_dim R rs hspan hdim i hi
    have hregI : IsRegularLocalRing (R ⧸ Ideal.ofList (rs.take i)) := hregi
    have hdomI := isDomain_of_isRegularLocalRing (R ⧸ Ideal.ofList (rs.take i))
    have hne : Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i] ≠ 0 := by
      intro hcon
      have hmem : rs[i] ∈ Ideal.ofList (rs.take i) :=
        Ideal.Quotient.eq_zero_iff_mem.mp hcon
      have hts := ofList_take_succ R rs i hilt
      have hle : Ideal.span {rs[i]} ≤ Ideal.ofList (rs.take i) :=
        Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
      have heq : Ideal.ofList (rs.take (i + 1)) =
          Ideal.ofList (rs.take i) := by
        rw [hts, sup_eq_left.mpr hle]
      have hdimS := (rung_regular_dim R rs hspan hdim (i + 1) hi1).2
      have he := Ideal.quotEquivOfEq heq
      have hde := ringKrullDim_eq_of_ringEquiv he
      rw [hdimS, hdimi] at hde
      have hcontra := nat_eq_of_dim_eq hde
      omega
    have htake : rs.take (i + 1) = rs.take i ++ [rs[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hilt]
      rfl
    rw [htake, isWeaklyRegular_append_iff]
    constructor
    · exact IH hi
    · rw [isWeaklyRegular_singleton_iff]
      have hJeq : Ideal.ofList (rs.take i) • (⊤ : Submodule R R) =
          (Ideal.ofList (rs.take i) : Submodule R R) :=
        QuotientByRegularIsCM.smul_top_eq_self _
      have e := Submodule.quotEquivOfEq _ _ hJeq
      have hregQ : IsSMulRegular (R ⧸ Ideal.ofList (rs.take i)) rs[i] := by
        intro m hm heq
        obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective m
        obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective hm
        have hsmul : ∀ u : R, rs[i] • Ideal.Quotient.mk
            (Ideal.ofList (rs.take i)) u =
            Ideal.Quotient.mk (Ideal.ofList (rs.take i)) rs[i] *
              Ideal.Quotient.mk (Ideal.ofList (rs.take i)) u := by
          intro u
          have h1 : rs[i] • Ideal.Quotient.mk (Ideal.ofList (rs.take i)) u =
              Ideal.Quotient.mk (Ideal.ofList (rs.take i)) (rs[i] • u) :=
            (Submodule.Quotient.mk_smul _ _ _).symm
          rw [h1, smul_eq_mul, map_mul]
        dsimp only at heq
        rw [← hs, ← ht, hsmul, hsmul] at heq
        have hcancel : Ideal.Quotient.mk (Ideal.ofList (rs.take i)) s =
            Ideal.Quotient.mk (Ideal.ofList (rs.take i)) t :=
          mul_left_cancel₀ hne heq
        rw [← hs, ← ht]
        exact hcancel
      intro m hm heq
      dsimp only at heq
      have h2 : e (rs[i] • m) = e (rs[i] • hm) := congrArg ⇑e heq
      rw [map_smul, map_smul] at h2
      have h3 : e m = e hm := hregQ h2
      exact e.injective h3

#print axioms rung_weaklyRegular

/-! ## §5 Grade assembly (design note §3.5, Matsumura Th 17.8) -/

/-- Main (design note §3.5, Matsumura Th 17.8 grade half): `dim ≤ grade` for
Noetherian regular local rings. The parameter list is regular: (c) gives
`IsWeaklyRegular R rs`, upgraded by
`of_isWeaklyRegular_of_mem_maximalIdeal` (entries in `𝔪`); then the
`GradeSet` witness + double-cast bridge (VariableInductionCM capstone pattern).
`hfin` is redundant (regularity forces `dim = ↑n`) and kept only for the
design note's exact signature. -/
theorem dim_le_grade_of_isRegularLocal (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hfin : ringKrullDim R < ⊤)
    (hreg : IsRegularLocal R) :
    ringKrullDim R ≤ ((GradeDepthFragment.grade R R
      (IsLocalRing.maximalIdeal R) : ℕ∞) : WithBot ℕ∞) := by
  have _hfin := hfin
  have hclass : IsRegularLocalRing R := regularClass_of_isRegularLocal R hreg
  obtain ⟨rs, hspan, _, hdimrs⟩ :=
    SystemOfParameters.exists_list_ofList_maximalIdeal R
  have hwreg : IsWeaklyRegular R rs := by
    have h := rung_weaklyRegular R rs hspan hdimrs rs.length le_rfl
    rwa [List.take_length] at h
  have hmem : ∀ r ∈ rs, r ∈ maximalIdeal R :=
    fun r hr => mem_maximal_of_mem_rs R rs hspan hr
  have hregSeq : IsRegular R rs :=
    IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R hmem hwreg
  have hmem' := GradeDepthFragment.mem_gradeSet_of_isRegular (R := R) (M := R)
    (IsLocalRing.maximalIdeal R) rs rfl hmem hregSeq
  have hge0 := GradeDepthFragment.le_grade_of_mem_gradeSet (R := R) (M := R)
    (I := IsLocalRing.maximalIdeal R) hmem'
  have hge : ((((rs.length : ℕ) : ℕ∞)) : WithBot ℕ∞) ≤
      ((GradeDepthFragment.grade R R (IsLocalRing.maximalIdeal R) : ℕ∞) :
        WithBot ℕ∞) := by
    exact_mod_cast hge0
  rw [WithBot.coe_natCast] at hge
  rw [hdimrs] at hge
  exact hge

#print axioms dim_le_grade_of_isRegularLocal

/-- Grade–dimension equality (Matsumura Th 17.8, `DepthEqDimAt` for regular
locals): `↑grade = dim` from main + the proved reverse
`GradeDepthFragment.grade_le_ringKrullDim`. -/
theorem grade_eq_dim_of_isRegularLocal (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hfin : ringKrullDim R < ⊤)
    (hreg : IsRegularLocal R) :
    ((GradeDepthFragment.grade R R (IsLocalRing.maximalIdeal R) : ℕ∞) :
      WithBot ℕ∞) = ringKrullDim R := by
  have hge := dim_le_grade_of_isRegularLocal R hfin hreg
  have hle := GradeDepthFragment.grade_le_ringKrullDim (R := R)
    (IsLocalRing.maximalIdeal R)
  exact le_antisymm hle hge

#print axioms grade_eq_dim_of_isRegularLocal

end DimLeGradeRegular
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
