/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Order.FixedPoints.Finset
public import Mathlib.Tactic

/-- A concrete monotone functional on `Finset (Fin 4)`: adjoin `0`
and shift every element up by one, capped at `3`. -/
private def stepUp (Z : Finset (Fin 4)) : Finset (Fin 4) :=
  insert 0 (Z.image (fun i => min (i + 1) 3))

private theorem stepUp_mono : Monotone stepUp := by
  intro Z₁ Z₂ hZ
  exact Finset.insert_subset_insert 0 (Finset.image_subset_image hZ)

/-- Iterating `stepUp` from `∅` reaches all of `Fin 4`. -/
example : Finset.lfpFin stepUp = Finset.univ := by decide

/-- The stabilization equation for `stepUp`. -/
example : stepUp (Finset.lfpFin stepUp) = Finset.lfpFin stepUp :=
  Finset.lfpFin_fixed stepUp_mono

/-- A concrete monotone functional on `Finset (Fin 4)`: cap every
element at `2`. -/
private def capTwo (Z : Finset (Fin 4)) : Finset (Fin 4) :=
  Z.image (fun i => min i 2)

private theorem capTwo_mono : Monotone capTwo := by
  intro Z₁ Z₂ hZ
  exact Finset.image_subset_image hZ

/-- Iterating `capTwo` from `Finset.univ` reaches `{0, 1, 2}`. -/
example : Finset.gfpFin capTwo = {0, 1, 2} := by decide

/-- The stabilization equation for `capTwo`. -/
example : capTwo (Finset.gfpFin capTwo) = Finset.gfpFin capTwo :=
  Finset.gfpFin_fixed capTwo_mono

/-- Park induction for `stepUp`: the least fixed point is contained
in every pre-fixed point, here `Finset.univ`. -/
example : Finset.lfpFin stepUp ⊆ Finset.univ :=
  Finset.lfpFin_le stepUp_mono (Finset.subset_univ _)

/-- Park coinduction for `capTwo`: every post-fixed point, here
`{0, 1}`, is contained in the greatest fixed point. -/
example : ({0, 1} : Finset (Fin 4)) ⊆ Finset.gfpFin capTwo :=
  Finset.le_gfpFin capTwo_mono (by decide)

/-- The bridge to predicate fixed points at the constant functional
`F _ s := s = 0` and its `Finset` counterpart `fun _ => {0}`. -/
example (s : Fin 4) :
    s ∈ Finset.lfpFin (fun _ : Finset (Fin 4) => {0}) ↔
      (⟨fun _ t => t = 0, fun _ _ _ _ ht => ht⟩ :
        (Fin 4 → Prop) →o (Fin 4 → Prop)).lfp s :=
  Finset.mem_lfpFin_iff_lfp (fun _ _ _ => Finset.Subset.rfl)
    (fun _ _ _ _ ht => ht) (fun _ t => by simp) s

/-- The dual bridge at the constant functional `F _ s := s = 0`. -/
example (s : Fin 4) :
    s ∈ Finset.gfpFin (fun _ : Finset (Fin 4) => {0}) ↔
      (⟨fun _ t => t = 0, fun _ _ _ _ ht => ht⟩ :
        (Fin 4 → Prop) →o (Fin 4 → Prop)).gfp s :=
  Finset.mem_gfpFin_iff_gfp (fun _ _ _ => Finset.Subset.rfl)
    (fun _ _ _ _ ht => ht) (fun _ t => by simp) s

#print axioms Finset.lfpFin_fixed
