/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryPrefixCancellation

/-!
# Positive Shih boundary coordinates

This file expresses positive upper and lower boundary terms in matching
coordinates, cancels the prefix stratum, and exposes the exact residual finite
types to be classified by the active-face and exceptional-survivor arguments.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

abbrev ShihUpperPositiveCoordinate (n : ℕ) :=
  ShihIndex (n + 1) × Fin (n + 2)

abbrev ShihLowerPositiveCoordinate (n : ℕ) :=
  ShihIndex n × Fin (n + 1)

def UpperPositiveCoordinate.IsPrefix {n : ℕ}
    (z : ShihUpperPositiveCoordinate n) : Prop :=
  z.2.val + 2 < z.1.gap

def LowerPositiveCoordinate.IsPrefix {n : ℕ}
    (z : ShihLowerPositiveCoordinate n) : Prop :=
  z.2.val + 1 < z.1.gap

abbrev ShihUpperPositivePrefixCoordinate (n : ℕ) :=
  {z : ShihUpperPositiveCoordinate n //
    UpperPositiveCoordinate.IsPrefix z}

abbrev ShihLowerPositivePrefixCoordinate (n : ℕ) :=
  {z : ShihLowerPositiveCoordinate n //
    LowerPositiveCoordinate.IsPrefix z}

abbrev ShihUpperPositiveResidualIndex (n : ℕ) :=
  {z : ShihUpperPositiveCoordinate n //
    ¬UpperPositiveCoordinate.IsPrefix z}

abbrev ShihLowerPositiveResidualIndex (n : ℕ) :=
  {z : ShihLowerPositiveCoordinate n //
    ¬LowerPositiveCoordinate.IsPrefix z}

noncomputable instance (n : ℕ) :
    Fintype (ShihUpperPositivePrefixCoordinate n) := by
  classical
  exact Subtype.fintype _

noncomputable instance (n : ℕ) :
    Fintype (ShihLowerPositivePrefixCoordinate n) := by
  classical
  exact Subtype.fintype _

noncomputable instance (n : ℕ) :
    Fintype (ShihUpperPositiveResidualIndex n) := by
  classical
  exact Subtype.fintype _

noncomputable instance (n : ℕ) :
    Fintype (ShihLowerPositiveResidualIndex n) := by
  classical
  exact Subtype.fintype _

/-- Removing one inactive prefix vertex preserves the predecessor coordinate
of a positive face. -/
def shihUpperPositiveCoordinatePrefixEquivLower (n : ℕ) :
    ShihUpperPositivePrefixCoordinate n ≃
      ShihLowerPositivePrefixCoordinate n where
  toFun z := by
    have hprefix := z.property
    change z.val.2.val + 2 < z.val.1.gap at hprefix
    let k : Fin (n + 1) := ⟨z.val.2.val, by
      have hdegree := z.val.1.p_add_q_add_gap
      omega⟩
    refine ⟨⟨z.val.1.lowerPrefix (by omega), k⟩, ?_⟩
    change k.val + 1 < (z.val.1.lowerPrefix (by omega)).gap
    simp only [k]
    have hgap := z.val.1.gap_lowerPrefix (by omega)
    omega
  invFun z := ⟨⟨z.val.1.raisePrefix, z.val.2.castSucc⟩, by
    change z.val.2.castSucc.val + 2 < z.val.1.raisePrefix.gap
    have hgap := z.val.1.gap_raisePrefix
    have h := z.property
    change z.val.2.val + 1 < z.val.1.gap at h
    simp only [Fin.val_castSucc]
    omega⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      rfl

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- Positive prefix terms cancel in the coordinates used by the remaining
positive-face sum. -/
theorem shihPositivePrefixCoordinate_sum_eq_zero
    (X Y : SimplicialObject C) (n : ℕ) :
    (∑ z : ShihUpperPositivePrefixCoordinate n,
        shihUpperBoundaryTerm X Y (n + 1) z.val.1 z.val.2.succ) +
      ∑ z : ShihLowerPositivePrefixCoordinate n,
        shihLowerBoundaryTerm X Y n z.val.2.succ z.val.1 = 0 := by
  classical
  rw [← (shihUpperPositiveCoordinatePrefixEquivLower n).sum_comp
    (fun z => shihLowerBoundaryTerm X Y n z.val.2.succ z.val.1)]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun z _ => by
    have hprefix : z.val.2.succ.val + 1 < z.val.1.gap := by
      have h := z.property
      change z.val.2.val + 2 < z.val.1.gap at h
      simpa only [Fin.val_succ] using h
    have hcancel := shihPrefixBoundaryTerm_add_eq_zero X Y
      z.val.1 z.val.2.succ hprefix
    have hindex :
        (shihUpperPositiveCoordinatePrefixEquivLower n z).val.1 =
          z.val.1.lowerPrefix (by omega) := by rfl
    have hface :
        (shihUpperPositiveCoordinatePrefixEquivLower n z).val.2.succ =
          z.val.1.lowerPrefixFace z.val.2.succ hprefix := by
      apply Fin.ext
      rfl
    rw [hindex, hface]
    exact hcancel

/-- Removing the positive prefix stratum leaves the exact residual upper and
lower finite sums. -/
theorem shihPositiveBoundary_sum_eq_residual
    (X Y : SimplicialObject C) (n : ℕ) :
    (∑ i : ShihIndex (n + 1),
        ∑ k : Fin (n + 2), shihUpperBoundaryTerm X Y (n + 1) i k.succ) +
      ∑ i : ShihIndex n,
        ∑ k : Fin (n + 1), shihLowerBoundaryTerm X Y n k.succ i =
    (∑ z : ShihUpperPositiveResidualIndex n,
        shihUpperBoundaryTerm X Y (n + 1) z.val.1 z.val.2.succ) +
      ∑ z : ShihLowerPositiveResidualIndex n,
        shihLowerBoundaryTerm X Y n z.val.2.succ z.val.1 := by
  classical
  have hUpper :
      (∑ i : ShihIndex (n + 1),
          ∑ k : Fin (n + 2), shihUpperBoundaryTerm X Y (n + 1) i k.succ) =
        (∑ z : ShihUpperPositivePrefixCoordinate n,
            shihUpperBoundaryTerm X Y (n + 1) z.val.1 z.val.2.succ) +
          ∑ z : ShihUpperPositiveResidualIndex n,
            shihUpperBoundaryTerm X Y (n + 1) z.val.1 z.val.2.succ := by
    calc
      _ = ∑ z : ShihUpperPositiveCoordinate n,
          shihUpperBoundaryTerm X Y (n + 1) z.1 z.2.succ :=
        (Fintype.sum_prod_type'
          (α₁ := ShihIndex (n + 1)) (α₂ := Fin (n + 2))
          (fun i k => shihUpperBoundaryTerm X Y (n + 1) i k.succ)).symm
      _ = _ := (Fintype.sum_subtype_add_sum_subtype
        UpperPositiveCoordinate.IsPrefix
        (fun z : ShihUpperPositiveCoordinate n =>
          shihUpperBoundaryTerm X Y (n + 1) z.1 z.2.succ)).symm
  have hLower :
      (∑ i : ShihIndex n,
          ∑ k : Fin (n + 1), shihLowerBoundaryTerm X Y n k.succ i) =
        (∑ z : ShihLowerPositivePrefixCoordinate n,
            shihLowerBoundaryTerm X Y n z.val.2.succ z.val.1) +
          ∑ z : ShihLowerPositiveResidualIndex n,
            shihLowerBoundaryTerm X Y n z.val.2.succ z.val.1 := by
    calc
      _ = ∑ z : ShihLowerPositiveCoordinate n,
          shihLowerBoundaryTerm X Y n z.2.succ z.1 :=
        (Fintype.sum_prod_type'
          (α₁ := ShihIndex n) (α₂ := Fin (n + 1))
          (fun i k => shihLowerBoundaryTerm X Y n k.succ i)).symm
      _ = _ := (Fintype.sum_subtype_add_sum_subtype
        LowerPositiveCoordinate.IsPrefix
        (fun z : ShihLowerPositiveCoordinate n =>
          shihLowerBoundaryTerm X Y n z.2.succ z.1)).symm
  rw [hUpper, hLower]
  have hprefix := shihPositivePrefixCoordinate_sum_eq_zero X Y n
  calc
    _ = ((∑ z : ShihUpperPositivePrefixCoordinate n,
            shihUpperBoundaryTerm X Y (n + 1) z.val.1 z.val.2.succ) +
          ∑ z : ShihLowerPositivePrefixCoordinate n,
            shihLowerBoundaryTerm X Y n z.val.2.succ z.val.1) +
        ((∑ z : ShihUpperPositiveResidualIndex n,
            shihUpperBoundaryTerm X Y (n + 1) z.val.1 z.val.2.succ) +
          ∑ z : ShihLowerPositiveResidualIndex n,
            shihLowerBoundaryTerm X Y n z.val.2.succ z.val.1) := by
      abel
    _ = _ := by rw [hprefix, zero_add]

end AlgebraicTopology.EilenbergZilber
