/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Local compactness of classical finite matrix groups

For every n∈ℕ, the complex unitary group U(n,ℂ) and real orthogonal group O(n,ℝ) are locally
compact in their induced finite-matrix topologies, including the singleton groups at n=0.
-/

@[expose] public section

noncomputable section

namespace Matrix

/-- **Local compactness of the finite complex unitary group.**

For n∈ℕ, the matrix group unitaryGroup(Fin n,ℂ)=U(n,ℂ) is locally compact in its induced
topology.
-/
instance unitaryGroupLocallyCompactSpace (n : ℕ) :
    LocallyCompactSpace (unitaryGroup (Fin n) ℂ) := by
  exact @IsClosed.locallyCompactSpace
    (Matrix (Fin n) (Fin n) ℂ) inferInstance
    (inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))) _
    (isClosed_unitary (R := Matrix (Fin n) (Fin n) ℂ))

/-- **Local compactness of the finite real orthogonal group.**

For n∈ℕ, the matrix group orthogonalGroup(Fin n,ℝ)=O(n,ℝ) is locally compact in its induced
topology.
-/
instance orthogonalGroupLocallyCompactSpace (n : ℕ) :
    LocallyCompactSpace (orthogonalGroup (Fin n) ℝ) := by
  exact @IsClosed.locallyCompactSpace
    (Matrix (Fin n) (Fin n) ℝ) inferInstance
    (inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))) _
    (isClosed_unitary (R := Matrix (Fin n) (Fin n) ℝ))

end Matrix

end
