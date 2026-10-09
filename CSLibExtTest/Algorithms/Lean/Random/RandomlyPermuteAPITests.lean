/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Random.RandomlyPermute

open Cslib.Algorithms.Lean.TimeM
open scoped BigOperators

universe u

example {α : Type u} {n : Nat} (xs : Vector α n)
    (draws : (i : Fin n) → Fin (n - i.val)) :
    (randomlyPermute xs draws).time = (n, n) := randomlyPermute_time xs draws

example {α : Type u} {n : Nat} (xs : Vector α n)
    (draws : (i : Fin n) → Fin (n - i.val)) :
    (randomlyPermute xs draws).ret.toList.Perm xs.toList := randomlyPermute_perm xs draws

example {α : Type u} (xs : Vector α 0) (draws : (i : Fin 0) → Fin (0 - i.val)) :
    randomlyPermute xs draws = ⟨xs, (0, 0)⟩ := randomlyPermute_empty xs draws

example {α : Type u} (xs : Vector α 1) (draws : (i : Fin 1) → Fin (1 - i.val)) :
    randomlyPermute xs draws = ⟨xs, (1, 1)⟩ := randomlyPermute_singleton xs draws

example {α : Type u} {n : Nat} (xs : Vector α n) :
    randomlyPermuteDistribution xs =
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).map
        (fun σ => (⟨Vector.ofFn (fun p => xs[(σ p).val]), (n, n)⟩ :
          Cslib.Algorithms.Lean.TimeM (Nat × Nat) (Vector α n))) :=
  randomlyPermuteDistribution_eq_map_uniform xs

open scoped Classical in
example {α : Type u} {n : Nat} (xs : Vector α n)
    (out : Cslib.Algorithms.Lean.TimeM (Nat × Nat) (Vector α n)) :
    randomlyPermuteDistribution xs out =
      ∑ draws : (i : Fin n) → Fin (n - i.val),
        if out = randomlyPermute xs draws
        then ∏ i : Fin n, ((n - i.val : Nat) : ENNReal)⁻¹ else 0 :=
  randomlyPermuteDistribution_apply xs out

example {n k : Nat} (hkn : k ≤ n) (a : Fin k → Fin n) (hinj : Function.Injective a) :
    (∑ draws : (i : Fin n) → Fin (n - i.val),
      if ∀ p : Fin k,
        (randomlyPermute (Vector.ofFn fun q : Fin n => q) draws).ret[(Fin.castLE hkn p).val] = a p
      then (n.factorial : ENNReal)⁻¹ else 0) =
        ((n - k).factorial : ENNReal) / n.factorial :=
  randomlyPermute_prefix_probability hkn a hinj

example {α : Type u} {n : Nat} (xs : Vector α n)
    (out : Cslib.Algorithms.Lean.TimeM (Nat × Nat) (Vector α n))
    (hcost : out.time ≠ (n, n)) : randomlyPermuteDistribution xs out = 0 := by
  classical
  rw [randomlyPermuteDistribution_apply]
  apply Finset.sum_eq_zero
  intro draws _
  have hne : out ≠ randomlyPermute xs draws := by
    intro h
    apply hcost
    rw [h]
    exact randomlyPermute_time xs draws
  simp only [hne, ↓reduceIte]

example {α : Type u} (xs : Vector α 0) :
    randomlyPermuteDistribution xs ⟨xs, (0, 0)⟩ = 1 := by
  classical
  rw [randomlyPermuteDistribution_apply]
  simp_rw [randomlyPermute_empty]
  simp

example {α : Type u} (xs : Vector α 1) :
    randomlyPermuteDistribution xs ⟨xs, (1, 1)⟩ = 1 := by
  classical
  rw [randomlyPermuteDistribution_apply]
  simp_rw [randomlyPermute_singleton]
  simp

example : randomlyPermuteDistribution (⟨#["a", "a", "b"], rfl⟩ : Vector String 3) =
    (PMF.uniformOfFintype (Equiv.Perm (Fin 3))).map
      (fun σ => (⟨Vector.ofFn (fun p =>
        (⟨#["a", "a", "b"], rfl⟩ : Vector String 3)[(σ p).val]), (3, 3)⟩ :
          Cslib.Algorithms.Lean.TimeM (Nat × Nat) (Vector String 3))) :=
  randomlyPermuteDistribution_eq_map_uniform _

#check @randomlyPermute
#check @randomlyPermuteDistribution
#check @randomlyPermuteDistribution_apply
