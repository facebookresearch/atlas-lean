/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Basic.Real.Basic

/-!
# Homogeneous point/vector action

The homogeneous block matrix of a linear map and a
translation distinguishes points from vectors through the
last extended coordinate: at `w = 1` it acts as the point
action `R *ᵥ q + p`, and at `w = 0` the translation
vanishes, leaving the vector action `R *ᵥ q`.
-/

@[expose] public section

open scoped Matrix

namespace ControlTheory

/-- The homogeneous block matrix of a linear map `R` and a
translation `p`, acting on extended coordinates indexed by
`m ⊕ Unit`: the linear block `R`, the translation column
`p`, a zero row, and the scalar `1`. -/
def homogeneousMatrix {m : Type*}
    (R : Matrix m m ℝ) (p : m → ℝ) :
    Matrix (m ⊕ Unit) (m ⊕ Unit) ℝ :=
  Matrix.fromBlocks R (Matrix.of fun i _ => p i) 0 1

/-- The homogeneous action distinguishes points from
vectors: on extended coordinates `Sum.elim q (fun _ => w)`,
the homogeneous matrix acts as
`Sum.elim (R *ᵥ q + w • p) (fun _ => w)`. At `w = 1` this
is the point action `R *ᵥ q + p`; at `w = 0` the translation
vanishes, the vector action. -/
theorem homogeneousMatrix_mulVec_elim {m : Type*} [Fintype m]
    (R : Matrix m m ℝ) (p q : m → ℝ) (w : ℝ) :
    homogeneousMatrix R p *ᵥ (Sum.elim q (fun _ => w))
      = Sum.elim (R *ᵥ q + w • p) (fun _ => w) := by
  unfold homogeneousMatrix
  rw [Matrix.fromBlocks_mulVec]
  have h1 : ((Sum.elim q (fun _ : Unit => w)) ∘ (Sum.inl : m → m ⊕ Unit)) = q := rfl
  have h2 : ((Sum.elim q (fun _ : Unit => w)) ∘ (Sum.inr : Unit → m ⊕ Unit))
      = (fun _ => w) := rfl
  rw [h1, h2, Matrix.zero_mulVec, Matrix.one_mulVec, zero_add]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, mul_comm, Pi.smul_apply, smul_eq_mul]

end ControlTheory
