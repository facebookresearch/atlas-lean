/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryPositiveCoordinates
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryMixedCancellation
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihPositiveFaceGate

/-!
# Arithmetic partition of the positive Shih boundary

After prefix cancellation, an upper positive coordinate is either the unique
transition face just before the active block or a face in the active block.
Every residual lower coordinate lies uniquely in the left or right active
boundary range.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

def UpperPositiveResidualIndex.IsTransition {n : ℕ}
    (z : ShihUpperPositiveResidualIndex n) : Prop :=
  z.val.2.val + 2 = z.val.1.gap

def UpperPositiveResidualIndex.IsActive {n : ℕ}
    (z : ShihUpperPositiveResidualIndex n) : Prop :=
  z.val.1.gap ≤ z.val.2.val + 1

abbrev ShihUpperPositiveTransitionIndex (n : ℕ) :=
  {z : ShihUpperPositiveResidualIndex n //
    UpperPositiveResidualIndex.IsTransition z}

abbrev ShihUpperPositiveActiveIndex (n : ℕ) :=
  {z : ShihUpperPositiveResidualIndex n //
    UpperPositiveResidualIndex.IsActive z}

noncomputable instance (n : ℕ) :
    Fintype (ShihUpperPositiveTransitionIndex n) := by
  classical
  exact Subtype.fintype _

noncomputable instance (n : ℕ) :
    Fintype (ShihUpperPositiveActiveIndex n) := by
  classical
  exact Subtype.fintype _

noncomputable def upperTransitionComplementEquivActive (n : ℕ) :
    {z : ShihUpperPositiveResidualIndex n //
      ¬UpperPositiveResidualIndex.IsTransition z} ≃
      ShihUpperPositiveActiveIndex n :=
  Equiv.subtypeEquivProp (by
    funext z
    apply propext
    constructor
    · intro h
      have hz := z.property
      change ¬z.val.2.val + 2 < z.val.1.gap at hz
      change z.val.2.val + 2 ≠ z.val.1.gap at h
      change z.val.1.gap ≤ z.val.2.val + 1
      omega
    · intro hactive htransition
      change z.val.1.gap ≤ z.val.2.val + 1 at hactive
      change z.val.2.val + 2 = z.val.1.gap at htransition
      omega)

/-- The exact transition/active partition of residual upper coordinates. -/
noncomputable def shihUpperPositiveResidualEquivTransitionSumActive (n : ℕ) :
    ShihUpperPositiveResidualIndex n ≃
      ShihUpperPositiveTransitionIndex n ⊕
        ShihUpperPositiveActiveIndex n := by
  classical
  exact (Equiv.sumCompl UpperPositiveResidualIndex.IsTransition).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (upperTransitionComplementEquivActive n))

/-- Sum form of the transition/active partition. -/
theorem sum_upperPositiveResidual_eq_transition_add_active
    {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : ShihUpperPositiveResidualIndex n → A) :
    ∑ z, f z =
      (∑ z : ShihUpperPositiveTransitionIndex n, f z.val) +
        ∑ z : ShihUpperPositiveActiveIndex n, f z.val := by
  classical
  calc
    _ = (∑ z : ShihUpperPositiveTransitionIndex n, f z.val) +
        ∑ z : {z : ShihUpperPositiveResidualIndex n //
          ¬UpperPositiveResidualIndex.IsTransition z}, f z.val :=
      (Fintype.sum_subtype_add_sum_subtype
        UpperPositiveResidualIndex.IsTransition f).symm
    _ = _ := by
      congr 1
      exact Fintype.sum_equiv (upperTransitionComplementEquivActive n)
        (fun z => f z.val) (fun z => f z.val) (fun _ => rfl)

/-- The active local shuffle face associated to a residual active upper
coordinate. -/
def ShihUpperPositiveActiveIndex.localFace {n : ℕ}
    (z : ShihUpperPositiveActiveIndex n) :
    Fin (z.val.val.1.p + 1 + z.val.val.1.q + 1) :=
  ⟨z.val.val.2.succ.val - z.val.val.1.gap, by
    have hsum := z.val.val.1.p_add_q_add_gap
    have hface := z.val.val.2.succ.isLt
    omega⟩

@[simp]
theorem ShihUpperPositiveActiveIndex.activeBoundaryFace_localFace
    {n : ℕ} (z : ShihUpperPositiveActiveIndex n) :
    z.val.val.1.activeBoundaryFace z.localFace = z.val.val.2.succ := by
  apply Fin.ext
  rw [ShihIndex.activeBoundaryFace]
  have hz := z.property
  change z.val.val.1.gap ≤ z.val.val.2.val + 1 at hz
  change z.val.val.1.gap +
    (z.val.val.2.succ.val - z.val.val.1.gap) = z.val.val.2.succ.val
  simp only [Fin.val_succ]
  omega

def LowerPositiveResidualIndex.IsLeft {n : ℕ}
    (z : ShihLowerPositiveResidualIndex n) : Prop :=
  z.val.2.succ.val ≤ z.val.1.gap + z.val.1.p

def LowerPositiveResidualIndex.IsRight {n : ℕ}
    (z : ShihLowerPositiveResidualIndex n) : Prop :=
  z.val.1.gap + z.val.1.p < z.val.2.succ.val

abbrev ShihLowerPositiveLeftIndex (n : ℕ) :=
  {z : ShihLowerPositiveResidualIndex n //
    LowerPositiveResidualIndex.IsLeft z}

abbrev ShihLowerPositiveRightIndex (n : ℕ) :=
  {z : ShihLowerPositiveResidualIndex n //
    LowerPositiveResidualIndex.IsRight z}

noncomputable instance (n : ℕ) :
    Fintype (ShihLowerPositiveLeftIndex n) := by
  classical
  exact Subtype.fintype _

noncomputable instance (n : ℕ) :
    Fintype (ShihLowerPositiveRightIndex n) := by
  classical
  exact Subtype.fintype _

noncomputable def lowerLeftComplementEquivRight (n : ℕ) :
    {z : ShihLowerPositiveResidualIndex n //
      ¬LowerPositiveResidualIndex.IsLeft z} ≃
      ShihLowerPositiveRightIndex n :=
  Equiv.subtypeEquivProp (by
    funext z
    apply propext
    constructor
    · intro h
      change ¬z.val.2.succ.val ≤ z.val.1.gap + z.val.1.p at h
      change z.val.1.gap + z.val.1.p < z.val.2.succ.val
      omega
    · intro h hleft
      change z.val.1.gap + z.val.1.p < z.val.2.succ.val at h
      change z.val.2.succ.val ≤ z.val.1.gap + z.val.1.p at hleft
      omega)

/-- The exact left/right partition of residual lower coordinates. -/
noncomputable def shihLowerPositiveResidualEquivLeftSumRight (n : ℕ) :
    ShihLowerPositiveResidualIndex n ≃
      ShihLowerPositiveLeftIndex n ⊕ ShihLowerPositiveRightIndex n := by
  classical
  exact (Equiv.sumCompl LowerPositiveResidualIndex.IsLeft).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (lowerLeftComplementEquivRight n))

/-- Sum form of the lower left/right partition. -/
theorem sum_lowerPositiveResidual_eq_left_add_right
    {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : ShihLowerPositiveResidualIndex n → A) :
    ∑ z, f z =
      (∑ z : ShihLowerPositiveLeftIndex n, f z.val) +
        ∑ z : ShihLowerPositiveRightIndex n, f z.val := by
  classical
  calc
    _ = (∑ z : ShihLowerPositiveLeftIndex n, f z.val) +
        ∑ z : {z : ShihLowerPositiveResidualIndex n //
          ¬LowerPositiveResidualIndex.IsLeft z}, f z.val :=
      (Fintype.sum_subtype_add_sum_subtype
        LowerPositiveResidualIndex.IsLeft f).symm
    _ = _ := by
      congr 1
      exact Fintype.sum_equiv (lowerLeftComplementEquivRight n)
        (fun z => f z.val) (fun z => f z.val) (fun _ => rfl)

/-- The inserted-left coordinate associated to a lower residual face in the
left range. -/
def ShihLowerPositiveLeftIndex.insertion {n : ℕ}
    (z : ShihLowerPositiveLeftIndex n) : Fin (z.val.val.1.p + 3) :=
  ⟨z.val.val.2.succ.val - (z.val.val.1.gap - 1), by
    have hleft := z.property
    change z.val.val.2.succ.val ≤
      z.val.val.1.gap + z.val.val.1.p at hleft
    have hgap := z.val.val.1.gap_pos
    omega⟩

theorem ShihLowerPositiveLeftIndex.insertion_pos {n : ℕ}
    (z : ShihLowerPositiveLeftIndex n) : 0 < z.insertion.val := by
  have hz := z.val.property
  change ¬z.val.val.2.val + 1 < z.val.val.1.gap at hz
  have hgap := z.val.val.1.gap_pos
  change 0 < z.val.val.2.succ.val - (z.val.val.1.gap - 1)
  simp only [Fin.val_succ]
  omega

theorem ShihLowerPositiveLeftIndex.insertion_lt_last {n : ℕ}
    (z : ShihLowerPositiveLeftIndex n) : z.insertion.val < z.val.val.1.p + 2 := by
  have hleft := z.property
  change z.val.val.2.succ.val ≤
    z.val.val.1.gap + z.val.val.1.p at hleft
  have hgap := z.val.val.1.gap_pos
  change z.val.val.2.succ.val - (z.val.val.1.gap - 1) <
    z.val.val.1.p + 2
  omega

theorem ShihLowerPositiveLeftIndex.face_val {n : ℕ}
    (z : ShihLowerPositiveLeftIndex n) :
    z.val.val.1.gap - 1 + z.insertion.val = z.val.val.2.succ.val := by
  have hz := z.val.property
  change ¬z.val.val.2.val + 1 < z.val.val.1.gap at hz
  have hgap := z.val.val.1.gap_pos
  change z.val.val.1.gap - 1 +
    (z.val.val.2.succ.val - (z.val.val.1.gap - 1)) =
      z.val.val.2.succ.val
  simp only [Fin.val_succ]
  omega

/-- The inserted-right coordinate associated to a lower residual face in the
right range. -/
def ShihLowerPositiveRightIndex.insertion {n : ℕ}
    (z : ShihLowerPositiveRightIndex n) : Fin (z.val.val.1.q + 2) :=
  ⟨z.val.val.2.succ.val - (z.val.val.1.gap + z.val.val.1.p), by
    have hsum := z.val.val.1.p_add_q_add_gap
    have hface := z.val.val.2.succ.isLt
    have hright := z.property
    change z.val.val.1.gap + z.val.val.1.p <
      z.val.val.2.succ.val at hright
    omega⟩

theorem ShihLowerPositiveRightIndex.insertion_pos {n : ℕ}
    (z : ShihLowerPositiveRightIndex n) : 0 < z.insertion.val := by
  have hz := z.property
  change z.val.val.1.gap + z.val.val.1.p <
    z.val.val.2.succ.val at hz
  change 0 < z.val.val.2.succ.val -
    (z.val.val.1.gap + z.val.val.1.p)
  omega

theorem ShihLowerPositiveRightIndex.face_val {n : ℕ}
    (z : ShihLowerPositiveRightIndex n) :
    z.val.val.1.gap + z.val.val.1.p + z.insertion.val =
      z.val.val.2.succ.val := by
  have hz := z.property
  change z.val.val.1.gap + z.val.val.1.p <
    z.val.val.2.succ.val at hz
  change z.val.val.1.gap + z.val.val.1.p +
    (z.val.val.2.succ.val -
      (z.val.val.1.gap + z.val.val.1.p)) = z.val.val.2.succ.val
  omega

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- The complete positive Shih boundary, after prefix cancellation, written as
the four disjoint residual strata used by the remaining cancellation proof. -/
theorem shihPositiveBoundary_sum_eq_partitioned
    (X Y : SimplicialObject C) (n : ℕ) :
    (∑ i : ShihIndex (n + 1),
        ∑ k : Fin (n + 2), shihUpperBoundaryTerm X Y (n + 1) i k.succ) +
      ∑ i : ShihIndex n,
        ∑ k : Fin (n + 1), shihLowerBoundaryTerm X Y n k.succ i =
    ((∑ z : ShihUpperPositiveTransitionIndex n,
        shihUpperBoundaryTerm X Y (n + 1)
          z.val.val.1 z.val.val.2.succ) +
      ∑ z : ShihUpperPositiveActiveIndex n,
        shihUpperBoundaryTerm X Y (n + 1)
          z.val.val.1 z.val.val.2.succ) +
    ((∑ z : ShihLowerPositiveLeftIndex n,
        shihLowerBoundaryTerm X Y n
          z.val.val.2.succ z.val.val.1) +
      ∑ z : ShihLowerPositiveRightIndex n,
        shihLowerBoundaryTerm X Y n
          z.val.val.2.succ z.val.val.1) := by
  rw [shihPositiveBoundary_sum_eq_residual]
  rw [sum_upperPositiveResidual_eq_transition_add_active,
    sum_lowerPositiveResidual_eq_left_add_right]

/-- The exact residual statement left after the arithmetic partition.  Its
four sums are respectively transition upper faces, active upper faces, left
lower faces, and right lower faces. -/
def ShihResidualFaceIdentity (X Y : SimplicialObject C) (n : ℕ) : Prop :=
  ((∑ z : ShihUpperPositiveTransitionIndex n,
      shihUpperBoundaryTerm X Y (n + 1)
        z.val.val.1 z.val.val.2.succ) +
    ∑ z : ShihUpperPositiveActiveIndex n,
      shihUpperBoundaryTerm X Y (n + 1)
        z.val.val.1 z.val.val.2.succ) +
  ((∑ z : ShihLowerPositiveLeftIndex n,
      shihLowerBoundaryTerm X Y n
        z.val.val.2.succ z.val.val.1) +
    ∑ z : ShihLowerPositiveRightIndex n,
      shihLowerBoundaryTerm X Y n
        z.val.val.2.succ z.val.val.1) =
    awShuffleZeroComponent X Y (n + 1) -
      𝟙 (X.obj (Opposite.op ⦋n + 1⦌) ⊗
        Y.obj (Opposite.op ⦋n + 1⦌))

/-- The original positive-face gate is equivalent to the four-stratum
residual identity. -/
theorem shihPositiveFaceIdentity_iff_residual
    (X Y : SimplicialObject C) (n : ℕ) :
    ShihPositiveFaceIdentity X Y n ↔ ShihResidualFaceIdentity X Y n := by
  rw [ShihPositiveFaceIdentity, ShihResidualFaceIdentity,
    shihPositiveBoundary_sum_eq_partitioned]

end AlgebraicTopology.EilenbergZilber
