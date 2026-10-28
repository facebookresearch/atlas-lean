/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairPrefix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairTailCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairCountTypes

/-! Exact decomposition of the original paired source solutions into their first two coordinates
and the 22 remaining coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The integer square sum of the paired prefix. -/
def leechNormSixPairPrefixSquare (p : Fin 17 × Fin 17) : ℕ :=
  (leechNormEightCoordinate p.1).natAbs ^ 2 + (leechNormEightCoordinate p.2).natAbs ^ 2

/-- Prefixes whose square sum fits the actual norm-six square sum. -/
def leechNormSixPairBoundedPrefix (m : Bool) (a b : ZMod 2) : Finset (Fin 17 × Fin 17) :=
  (leechNormSixPairPrefix m a b).filter fun p => leechNormSixPairPrefixSquare p ≤ 48

/-- Exactly the permitted source prefixes, before counting the remaining coordinates. -/
def LeechNormSixPairPrefixChoice (m : Bool) (a b : ZMod 2) :=
  {p // p ∈ leechNormSixPairBoundedPrefix m a b}

/-- Source solutions split at the fixed pair; their remaining square sum and height are exact. -/
def LeechNormSixPairParts (m : Bool) (c : golayCode) :=
  Σ p : LeechNormSixPairPrefixChoice m (c.val 0) (c.val 1),
    LeechNormSixTailSolution m (fun i => c.val i.succ.succ)
      (48 - leechNormSixPairPrefixSquare p.val) (4 * (m.toNat : ZMod 8) - 4)

/-- Joining the prefix and tail reconstructs every original source coordinate. -/
def leechNormSixPairPartsVector (m : Bool) (c : golayCode) :
    LeechNormSixPairParts m c → LeechNormSixPairBoundedSolution m c := by
  intro s
  let a : Fin 17 := s.1.val.1
  let b : Fin 17 := s.1.val.2
  let t : Fin 22 → Fin 17 := s.2.val
  refine ⟨Fin.cons a (Fin.cons b t), ?_⟩
  have hp := s.1.property
  have ht := s.2.property
  obtain ⟨hp, hn⟩ := Finset.mem_filter.mp hp
  have h01 : (0 : Fin 23).succ = (1 : Fin 24) := by decide
  have hr :
      (leechNormEightCoordinate a : ZMod 4) =
        (m.toNat : ZMod 4) + 2 * ((c.val 0).val : ZMod 4) ∧
      (leechNormEightCoordinate b : ZMod 4) =
        (m.toNat : ZMod 4) + 2 * ((c.val 1).val : ZMod 4) ∧
      leechNormEightCoordinate a + leechNormEightCoordinate b = 4 := by
    simpa only [leechNormSixPairPrefix, Finset.mem_filter, Finset.mem_univ, true_and] using hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    cases i using Fin.cases with
    | zero => simpa only [Fin.cons_zero] using hr.1
    | succ j =>
      cases j using Fin.cases with
      | zero => simpa only [h01, Fin.cons_one, Fin.cons_zero] using hr.2.1
      | succ k => simpa only [Fin.cons_succ] using ht.1 k
  · rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have h : (∑ i, (leechNormEightCoordinate (t i)).natAbs ^ 2) =
        48 - ((leechNormEightCoordinate a).natAbs ^ 2 +
          (leechNormEightCoordinate b).natAbs ^ 2) := ht.2.1
    have hn' : (leechNormEightCoordinate a).natAbs ^ 2 +
        (leechNormEightCoordinate b).natAbs ^ 2 ≤ 48 := hn
    omega
  · have he : (∑ i : Fin 24,
        leechNormEightCoordinate ((Fin.cons a (Fin.cons b t) : Fin 24 → Fin 17) i)) =
        leechNormEightCoordinate a + leechNormEightCoordinate b +
          ∑ i : Fin 22, leechNormEightCoordinate (t i) := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      abel
    rw [he, hr.2.2, Int.cast_add, Int.cast_ofNat, ht.2.2]
    abel
  · simpa only [Fin.cons_zero, Fin.cons_one] using hr.2.2

/-- The original interval addresses make this reconstruction injective. -/
theorem leechNormSixPairPartsVector_injective (m : Bool) (c : golayCode) :
    Function.Injective (leechNormSixPairPartsVector m c) := by
  rintro ⟨p, t⟩ ⟨q, v⟩ h
  have ha := congrArg (fun u => u.val 0) h
  have hb := congrArg (fun u => u.val 1) h
  simp only [leechNormSixPairPartsVector, Fin.cons_zero] at ha
  simp only [leechNormSixPairPartsVector, Fin.cons_one] at hb
  have hp : p = q := Subtype.ext (Prod.ext ha hb)
  subst q
  have ht : t = v := by
    apply Subtype.ext
    funext i
    have hi := congrArg (fun u => u.val i.succ.succ) h
    simpa only [leechNormSixPairPartsVector, Fin.cons_succ] using hi
  subst v
  rfl

/-- Every original source solution has exactly its two prefix coordinates and its remaining tail. -/
theorem leechNormSixPairPartsVector_surjective (m : Bool) (c : golayCode) :
    Function.Surjective (leechNormSixPairPartsVector m c) := by
  rintro ⟨u, hu⟩
  have h01 : (0 : Fin 23).succ = (1 : Fin 24) := by decide
  let p : Fin 17 × Fin 17 := (u 0, u 1)
  let t : Fin 22 → Fin 17 := fun i => u i.succ.succ
  have hn : leechNormSixPairPrefixSquare p +
      (∑ i : Fin 22, (leechNormEightCoordinate (t i)).natAbs ^ 2) = 48 := by
    have h := hu.2.1
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h
    simpa only [leechNormSixPairPrefixSquare, p, t, add_assoc, h01] using h
  have hp : p ∈ leechNormSixPairBoundedPrefix m (c.val 0) (c.val 1) := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, by omega⟩
    simp only [leechNormSixPairPrefix, Finset.mem_filter, Finset.mem_univ, true_and, p]
    exact ⟨hu.1 0, hu.1 1, hu.2.2.2⟩
  have ht :
      (∀ i, (leechNormEightCoordinate (t i) : ZMod 4) =
        (m.toNat : ZMod 4) + 2 * ((c.val i.succ.succ).val : ZMod 4)) ∧
      (∑ i, (leechNormEightCoordinate (t i)).natAbs ^ 2) =
        48 - leechNormSixPairPrefixSquare p ∧
      ((∑ i, leechNormEightCoordinate (t i) : ℤ) : ZMod 8) =
        4 * (m.toNat : ZMod 8) - 4 := by
    refine ⟨fun i => hu.1 i.succ.succ, by omega, ?_⟩
    have he : (∑ i : Fin 24, leechNormEightCoordinate (u i)) =
        leechNormEightCoordinate (u 0) + leechNormEightCoordinate (u 1) +
          ∑ i : Fin 22, leechNormEightCoordinate (t i) := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [t, h01]
      abel
    have h := hu.2.2.1
    rw [he, hu.2.2.2, Int.cast_add, Int.cast_ofNat] at h
    linear_combination h
  refine ⟨⟨⟨p, hp⟩, ⟨t, ht⟩⟩, ?_⟩
  apply Subtype.ext
  funext i
  cases i using Fin.cases with
  | zero => simp [leechNormSixPairPartsVector, p]
  | succ j =>
    cases j using Fin.cases with
    | zero => simp [leechNormSixPairPartsVector, p]
    | succ k => simp [leechNormSixPairPartsVector, t]

/-- Exact source decomposition, with no omitted prefix or tail. -/
noncomputable def leechNormSixPairPartsEquiv (m : Bool) (c : golayCode) :
    LeechNormSixPairParts m c ≃ LeechNormSixPairBoundedSolution m c :=
  Equiv.ofBijective (leechNormSixPairPartsVector m c)
    ⟨leechNormSixPairPartsVector_injective m c, leechNormSixPairPartsVector_surjective m c⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
