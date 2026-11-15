/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite-class PAC learnability: counting core

Samples of size `m` from a finite domain `X` are the `|X| ^ m` functions `Fin m → X`. A
hypothesis that disagrees with the target somewhere is consistent with at most
`(|X| - 1) ^ m` of them, so a union bound over a finite class leaves a sample on which only
hypotheses agreeing with the target everywhere are consistent. This is the counting form of
the finite-class argument: no distribution, accuracy, or confidence parameter appears. The
measure-theoretic finite-class PAC bound is
`Cslib.MachineLearning.PACLearning.IsConsistent.failure_le_exp` in
`CSLibExt/MachineLearning/PACLearning/FiniteClass.lean`.
-/

@[expose] public section

/-- A hypothesis `h` is consistent with the target `c` on a sample `s : Fin m → X` when it
agrees with `c` at every sampled point. The number of such samples is `a ^ m`, where `a` is the
number of points at which `h` and `c` agree. -/
theorem card_consistent {X : Type*} [Fintype X] [DecidableEq X]
    (c h : X → Bool) (m : ℕ) :
    (Finset.univ.filter (fun s : Fin m → X => ∀ i, h (s i) = c (s i))).card
      = (Finset.univ.filter (fun x => h x = c x)).card ^ m := by
  have h1 : (Finset.univ.filter (fun s : Fin m → X => ∀ i, h (s i) = c (s i))).card
      = Fintype.card {s : Fin m → X // ∀ i, h (s i) = c (s i)} := by
    rw [← Fintype.card_subtype]
  have h2 : (Finset.univ.filter (fun x => h x = c x)).card
      = Fintype.card {x // h x = c x} := by
    rw [← Fintype.card_subtype]
  rw [h1, h2]
  let e : {s : Fin m → X // ∀ i, h (s i) = c (s i)} ≃ (Fin m → {x // h x = c x}) :=
    { toFun := fun s i => ⟨s.1 i, s.2 i⟩
      invFun := fun f => ⟨fun i => (f i).1, fun i => (f i).2⟩
      left_inv := fun s => by simp
      right_inv := fun f => by simp }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]

/-- If `h` disagrees with `c` somewhere, its agreement set has
at most `|X| - 1` points, so it is consistent on at most
`(|X| - 1) ^ m` samples. -/
theorem card_consistent_le {X : Type*} [Fintype X] [DecidableEq X]
    (c h : X → Bool) (m : ℕ) (hdis : ∃ x, h x ≠ c x) :
    (Finset.univ.filter (fun s : Fin m → X => ∀ i, h (s i) = c (s i))).card
      ≤ (Fintype.card X - 1) ^ m := by
  rw [card_consistent]
  obtain ⟨x0, hx0⟩ := hdis
  have hmem : x0 ∉ Finset.univ.filter (fun x => h x = c x) := by
    simp [hx0]
  have hlt : (Finset.univ.filter (fun x => h x = c x)).card < Fintype.card X :=
    Finset.card_lt_univ_of_notMem hmem
  have hle : (Finset.univ.filter (fun x => h x = c x)).card ≤ Fintype.card X - 1 := by
    omega
  exact Nat.pow_le_pow_left hle m

/-- Existence form: if the whole finite class `C` has
`|C| * (|X| - 1) ^ m < |X| ^ m`, some sample is consistent
only with hypotheses agreeing with `c` everywhere on `X`
(any `h in C` consistent on it equals `c`). -/
theorem exists_sample_kills_bad {X : Type*} [Fintype X] [DecidableEq X]
    (c : X → Bool) (C : Finset (X → Bool)) (m : ℕ)
    (hcount : C.card * (Fintype.card X - 1) ^ m < (Fintype.card X) ^ m) :
    ∃ s : Fin m → X, ∀ h ∈ C, (∀ i, h (s i) = c (s i)) → h = c := by
  classical
  have hcardT : ((C.filter (fun h => ∃ x, h x ≠ c x)).biUnion
      (fun h => Finset.univ.filter (fun s : Fin m → X => ∀ i, h (s i) = c (s i)))).card
      ≤ C.card * (Fintype.card X - 1) ^ m := by
    calc ((C.filter (fun h => ∃ x, h x ≠ c x)).biUnion
          (fun h => Finset.univ.filter (fun s : Fin m → X => ∀ i, h (s i) = c (s i)))).card
          ≤ ∑ h ∈ (C.filter (fun h => ∃ x, h x ≠ c x)),
            (Finset.univ.filter (fun s : Fin m → X => ∀ i, h (s i) = c (s i))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ h ∈ (C.filter (fun h => ∃ x, h x ≠ c x)), (Fintype.card X - 1) ^ m := by
            apply Finset.sum_le_sum
            intro h hh
            have hdis : ∃ x, h x ≠ c x := (Finset.mem_filter.mp hh).2
            exact card_consistent_le c h m hdis
        _ = (C.filter (fun h => ∃ x, h x ≠ c x)).card * (Fintype.card X - 1) ^ m := by
            simp [Finset.sum_const]
        _ ≤ C.card * (Fintype.card X - 1) ^ m := by
            apply Nat.mul_le_mul_right
            exact Finset.card_filter_le C _
  have huniv : (Finset.univ : Finset (Fin m → X)).card = (Fintype.card X) ^ m := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  have hTne : (C.filter (fun h => ∃ x, h x ≠ c x)).biUnion
      (fun h => Finset.univ.filter (fun s : Fin m → X => ∀ i, h (s i) = c (s i))) ≠
        Finset.univ := by
    intro heq
    rw [heq, huniv] at hcardT
    exact Nat.not_le_of_gt hcount hcardT
  obtain ⟨s, hs⟩ : ∃ s : Fin m → X, s ∉ (C.filter (fun h => ∃ x, h x ≠ c x)).biUnion
      (fun h => Finset.univ.filter (fun s : Fin m → X => ∀ i, h (s i) = c (s i))) := by
    have hnotall : ¬ ∀ x, x ∈ (C.filter (fun h => ∃ x, h x ≠ c x)).biUnion
        (fun h => Finset.univ.filter (fun s : Fin m → X => ∀ i, h (s i) = c (s i))) := by
      intro hall
      exact hTne (Finset.eq_univ_iff_forall.mpr hall)
    exact not_forall.mp hnotall
  refine ⟨s, fun h hh hcon => ?_⟩
  have hnotbad : ¬ ∃ x, h x ≠ c x := by
    intro hex
    have hBmem : h ∈ C.filter (fun h => ∃ x, h x ≠ c x) := Finset.mem_filter.mpr ⟨hh, hex⟩
    have hsmem : s ∈ Finset.univ.filter (fun s : Fin m → X => ∀ i, h (s i) = c (s i)) := by
      simp [hcon]
    have hmem : s ∈ (C.filter (fun h => ∃ x, h x ≠ c x)).biUnion
        (fun h => Finset.univ.filter (fun s : Fin m → X => ∀ i, h (s i) = c (s i))) :=
      Finset.mem_biUnion.mpr ⟨h, hBmem, hsmem⟩
    exact hs hmem
  have hall : ∀ x, h x = c x := fun x => of_not_not (fun he => hnotbad ⟨x, he⟩)
  exact funext hall

end
