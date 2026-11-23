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
      (Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm (Fin n))).map
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
    (Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm (Fin 3))).map
      (fun σ => (⟨Vector.ofFn (fun p =>
        (⟨#["a", "a", "b"], rfl⟩ : Vector String 3)[(σ p).val]), (3, 3)⟩ :
          Cslib.Algorithms.Lean.TimeM (Nat × Nat) (Vector String 3))) :=
  randomlyPermuteDistribution_eq_map_uniform _

-- Fisher–Yates' list law is `uniformPermutation`
example {α : Type u} {n : Nat} (xs : Vector α n) :
    (randomlyPermuteDistribution xs).map (fun r => r.ret.toList) =
      uniformPermutation xs.toList :=
  randomlyPermuteDistribution_map_toList xs

-- so an expected cost over `uniformPermutation` is the expected cost after Fisher–Yates
example {α β : Type} {n : Nat} (algo : List α → Cslib.Algorithms.Lean.TimeM Nat β)
    (xs : Vector α n) :
    expectedTime algo (uniformPermutation xs.toList) =
      (randomlyPermuteDistribution xs).expectENN
        (fun r => ((algo r.ret.toList).time : ENNReal)) := by
  rw [expectedTime, ← randomlyPermuteDistribution_map_toList, PMF.expectENN_map]
  rfl

example : (randomlyPermuteDistribution (⟨#["a", "a", "b"], rfl⟩ : Vector String 3)).map
      (fun r => r.ret.toList) = uniformPermutation ["a", "a", "b"] :=
  randomlyPermuteDistribution_map_toList _

-- Boundary: the bridge needs neither a nonempty element type nor a positive length.
example :
    (randomlyPermuteDistribution (⟨#[], rfl⟩ : Vector Empty 0)).map
        (fun out => out.ret.toList) = uniformPermutation ([] : List Empty) :=
  randomlyPermuteDistribution_map_toList _

-- Boundary: the singleton case goes through the same map/toList path.
example {α : Type u} (a : α) :
    (randomlyPermuteDistribution (⟨#[a], rfl⟩ : Vector α 1)).map
        (fun out => out.ret.toList) = uniformPermutation [a] :=
  randomlyPermuteDistribution_map_toList _

-- Multiplicity on another type: repeated entries need no distinctness hypothesis.
example :
    (randomlyPermuteDistribution (⟨#[true, false, true], rfl⟩ : Vector Bool 3)).map
        (fun out => out.ret.toList) = uniformPermutation [true, false, true] :=
  randomlyPermuteDistribution_map_toList _

-- Closed end-to-end expected cost after execution. This exercises the expectENN transfer,
-- not uniformity: the length cost is constant, hence identical on every permutation.
example : expectedTime
    (fun xs : List Bool => (⟨(), xs.length⟩ : Cslib.Algorithms.Lean.TimeM Nat Unit))
    ((randomlyPermuteDistribution (⟨#[true, false, true], rfl⟩ : Vector Bool 3)).map
      (fun out => out.ret.toList)) = (3 : ENNReal) := by
  rw [randomlyPermuteDistribution_map_toList]
  exact expectedTime_uniformPermutation_eq_of_time_eq _ _ 3 (fun _ => List.length_ofFn)

#print axioms Cslib.Algorithms.Lean.TimeM.randomlyPermuteDistribution_map_toList

#check @randomlyPermute
#check @randomlyPermuteDistribution
#check @randomlyPermuteDistribution_apply
#check @randomlyPermuteDistribution_map_toList
