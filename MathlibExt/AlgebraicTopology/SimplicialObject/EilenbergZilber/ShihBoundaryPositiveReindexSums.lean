/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryPositiveReindex

/-!
# Sum-level reindexing of the residual positive Shih boundary

The finite equivalences are applied here, separately from their combinatorial
construction, to expose the four canonical summation families.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

theorem sum_upperPositiveTransition_eq_shihIndex
    {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : ShihUpperPositiveTransitionIndex n → A) :
    ∑ z, f z = ∑ i : ShihIndex n, f ((shihUpperPositiveTransitionEquiv n).symm i) :=
  Fintype.sum_equiv (shihUpperPositiveTransitionEquiv n) _ _ fun _ => by simp

theorem sum_upperPositiveActive_eq_data
    {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : ShihUpperPositiveActiveIndex n → A) :
    ∑ z, f z = ∑ z : ShihUpperActiveData n,
      f ((shihUpperPositiveActiveEquiv n).symm z) :=
  Fintype.sum_equiv (shihUpperPositiveActiveEquiv n) _ _ fun _ => by simp

theorem sum_lowerPositiveLeft_eq_data
    {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : ShihLowerPositiveLeftIndex n → A) :
    ∑ z, f z = ∑ z : ShihLowerLeftData n,
      f ((shihLowerPositiveLeftEquiv n).symm z) :=
  Fintype.sum_equiv (shihLowerPositiveLeftEquiv n) _ _ fun _ => by simp

theorem sum_lowerPositiveRight_eq_data
    {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : ShihLowerPositiveRightIndex n → A) :
    ∑ z, f z = ∑ z : ShihLowerRightData n,
      f ((shihLowerPositiveRightEquiv n).symm z) :=
  Fintype.sum_equiv (shihLowerPositiveRightEquiv n) _ _ fun _ => by simp

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- The positive boundary after prefix cancellation and all four canonical
finite reindexings.  No categorical cancellation is used in this theorem. -/
theorem shihPositiveBoundary_sum_eq_reindexed
    (X Y : SimplicialObject C) (n : ℕ) :
    (∑ i : ShihIndex (n + 1),
        ∑ k : Fin (n + 2), shihUpperBoundaryTerm X Y (n + 1) i k.succ) +
      ∑ i : ShihIndex n,
        ∑ k : Fin (n + 1), shihLowerBoundaryTerm X Y n k.succ i =
    ((∑ i : ShihIndex n,
        let z := (shihUpperPositiveTransitionEquiv n).symm i
        shihUpperBoundaryTerm X Y (n + 1)
          z.val.val.1 z.val.val.2.succ) +
      ∑ z : ShihUpperActiveData n,
        let w := (shihUpperPositiveActiveEquiv n).symm z
        shihUpperBoundaryTerm X Y (n + 1)
          w.val.val.1 w.val.val.2.succ) +
    ((∑ z : ShihLowerLeftData n,
        let w := (shihLowerPositiveLeftEquiv n).symm z
        shihLowerBoundaryTerm X Y n w.val.val.2.succ w.val.val.1) +
      ∑ z : ShihLowerRightData n,
        let w := (shihLowerPositiveRightEquiv n).symm z
        shihLowerBoundaryTerm X Y n w.val.val.2.succ w.val.val.1) := by
  rw [shihPositiveBoundary_sum_eq_partitioned,
    sum_upperPositiveTransition_eq_shihIndex,
    sum_upperPositiveActive_eq_data,
    sum_lowerPositiveLeft_eq_data,
    sum_lowerPositiveRight_eq_data]

/-- The positive-face goal in canonical transition/active/left/right
coordinates. -/
def ShihReindexedPositiveFaceIdentity
    (X Y : SimplicialObject C) (n : ℕ) : Prop :=
  ((∑ i : ShihIndex n,
      let z := (shihUpperPositiveTransitionEquiv n).symm i
      shihUpperBoundaryTerm X Y (n + 1)
        z.val.val.1 z.val.val.2.succ) +
    ∑ z : ShihUpperActiveData n,
      let w := (shihUpperPositiveActiveEquiv n).symm z
      shihUpperBoundaryTerm X Y (n + 1)
        w.val.val.1 w.val.val.2.succ) +
  ((∑ z : ShihLowerLeftData n,
      let w := (shihLowerPositiveLeftEquiv n).symm z
      shihLowerBoundaryTerm X Y n w.val.val.2.succ w.val.val.1) +
    ∑ z : ShihLowerRightData n,
      let w := (shihLowerPositiveRightEquiv n).symm z
      shihLowerBoundaryTerm X Y n w.val.val.2.succ w.val.val.1) =
    awShuffleZeroComponent X Y (n + 1) -
      𝟙 (X.obj (Opposite.op ⦋n + 1⦌) ⊗
        Y.obj (Opposite.op ⦋n + 1⦌))

/-- The original positive-face gate is equivalent to its fully reindexed
transition/active/left/right form. -/
theorem shihPositiveFaceIdentity_iff_reindexed
    (X Y : SimplicialObject C) (n : ℕ) :
    ShihPositiveFaceIdentity X Y n ↔
      ShihReindexedPositiveFaceIdentity X Y n := by
  rw [ShihPositiveFaceIdentity, ShihReindexedPositiveFaceIdentity,
    shihPositiveBoundary_sum_eq_reindexed]

end AlgebraicTopology.EilenbergZilber
