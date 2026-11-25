/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryPositiveReindexSums
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryIntrinsicCancellation

/-!
# Transition cancellation in canonical residual coordinates
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

namespace ShihIndex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- A raised-prefix transition term cancels its initial left insertion. -/
theorem raisePrefixTerm_add_leftZeroTerm_eq_zero
    (X Y : SimplicialObject C) {n : ℕ} (i : ShihIndex n) :
    shihUpperBoundaryTerm X Y (n + 1) i.raisePrefix
        (i.leftUpperFaceOf 0) +
      shihUpperBoundaryTerm X Y (n + 1) (i.leftUpperOf 0)
        (i.leftUpperFaceOf 0) = 0 := by
  rcases i with ⟨⟨p, hp⟩, ⟨q, hq⟩, t⟩
  generalize hgap : n - p - q = m
  have hm : 0 < m := by
    have hq' : q < n - p := hq
    omega
  have hdegree : p + q + m = n := by omega
  have h := shihTransitionBoundaryTerm_add_leftZero_eq_zero
    X Y p q m hm t
  have hn : n = p + q + m := hdegree.symm
  subst n
  convert h using 1;
    simp only [raisePrefix, leftUpperOf, leftUpperFaceOf,
      ofGap, transitionUpperFace, leftBoundaryUpperIndex,
      leftBoundaryUpperFace, Shuffle.leftBoundaryIndex_zero,
      gap, hgap, Fin.val_zero, Nat.add_zero]

end ShihIndex

/-- Each transition coordinate, transported by
`shihUpperPositiveTransitionEquiv`, cancels its initial left-insertion
coordinate. -/
theorem transitionCoordinateTerm_add_leftZeroTerm_eq_zero
    {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (X Y : SimplicialObject C) {n : ℕ} (i : ShihIndex n) :
    let z := (shihUpperPositiveTransitionEquiv n).symm i
    shihUpperBoundaryTerm X Y (n + 1)
        z.val.val.1 z.val.val.2.succ +
      shihUpperBoundaryTerm X Y (n + 1) (i.leftUpperOf 0)
        (i.leftUpperFaceOf 0) = 0 := by
  dsimp only
  have hindex :
      ((shihUpperPositiveTransitionEquiv n).symm i).val.val.1 =
        i.raisePrefix := rfl
  have hface :
      ((shihUpperPositiveTransitionEquiv n).symm i).val.val.2.succ =
        i.leftUpperFaceOf 0 := by
    have ht := ((shihUpperPositiveTransitionEquiv n).symm i).property
    change
      ((shihUpperPositiveTransitionEquiv n).symm i).val.val.2.val + 2 =
        ((shihUpperPositiveTransitionEquiv n).symm i).val.val.1.gap at ht
    rw [hindex, i.gap_raisePrefix] at ht
    apply Fin.ext
    simp only [ShihIndex.leftUpperFaceOf,
      Shuffle.leftBoundaryIndex_zero, Fin.val_succ, Fin.val_zero,
      Nat.add_zero]
    omega
  rw [hindex, hface]
  exact i.raisePrefixTerm_add_leftZeroTerm_eq_zero X Y

/-- The reindexed transition sum cancels the complete initial-left insertion
family. -/
theorem transitionSum_add_leftZeroSum_eq_zero
    {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (X Y : SimplicialObject C) (n : ℕ) :
    (∑ z : ShihUpperPositiveTransitionIndex n,
        shihUpperBoundaryTerm X Y (n + 1)
          z.val.val.1 z.val.val.2.succ) +
      ∑ i : ShihIndex n,
        shihUpperBoundaryTerm X Y (n + 1) (i.leftUpperOf 0)
          (i.leftUpperFaceOf 0) = 0 := by
  rw [sum_upperPositiveTransition_eq_shihIndex,
    ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun i _ =>
    transitionCoordinateTerm_add_leftZeroTerm_eq_zero X Y i

end AlgebraicTopology.EilenbergZilber
