/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic
public import MathlibExt.Biology.Dynamics.PlanarStability
public import MathlibExt.LinearAlgebra.Matrix.MMatrix

/-!
# Planar Jacobian criterion for rate equilibria

For a planar rate equilibrium, the Jacobian criterion is the
existing planar trace-determinant Hurwitz equivalence: negative
trace and positive determinant exactly characterize Hurwitz
Jacobians. The negative identity is the zero-gain boundary
witness. This module records only that matrix criterion; any
stability conclusion for a specific field additionally needs
that field's equilibrium, Jacobian, and solution hypotheses.
-/

@[expose] public section

namespace MathlibExt.Biology.Biophysics.NeuralPopulation.Stability

/-- **Planar trace-determinant Hurwitz criterion.** A real
planar matrix is Hurwitz exactly when its trace is negative and
its determinant is positive, by the existing planar stability
equivalence. -/
theorem trace_det_isHurwitz {A : Matrix (Fin 2) (Fin 2) ℝ}
    (htr : A.trace < 0) (hdet : 0 < A.det) : A.IsHurwitz :=
  (MathlibExt.Biology.Dynamics.PlanarStability.isHurwitz_iff_trace_neg_and_det_pos A).mpr
    ⟨htr, hdet⟩

/-- **Boundary-equilibrium witness.** The negative identity on
the plane, the Jacobian at the zero-gain boundary equilibrium,
is Hurwitz. -/
theorem neg_identity_isHurwitz :
    ((-1 : Matrix (Fin 2) (Fin 2) ℝ)).IsHurwitz := by
  have h : ((-1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).IsHurwitz :=
    Matrix.isHurwitz_smul_one (by norm_num)
  simpa using h

/-- The negative identity has trace `-2` and determinant `1`:
the boundary witness meets the trace-determinant signs. -/
theorem neg_identity_trace_det :
    (-1 : Matrix (Fin 2) (Fin 2) ℝ).trace = -2 ∧
      (-1 : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  simp [Matrix.det_fin_two]

end MathlibExt.Biology.Biophysics.NeuralPopulation.Stability
