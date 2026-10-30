/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

/-!
# AlgebraNotes canonical API reuse tests

Canonical affine-isometry linear data and integer-submodule lattice APIs.
These tests do not identify operator distance with a rotation angle or prove a plane classification.
-/

namespace AlgebraNotesApiProbe

private theorem translated_point (f : EuclideanSpace ℝ (Fin 2) ≃ᵃⁱ[ℝ]
    EuclideanSpace ℝ (Fin 2)) (p v : EuclideanSpace ℝ (Fin 2)) :
    f (v +ᵥ p) = f.linearIsometryEquiv v +ᵥ f p :=
  AffineIsometryEquiv.map_vadd f p v

private theorem linear_part_difference (f : EuclideanSpace ℝ (Fin 2) ≃ᵃⁱ[ℝ]
    EuclideanSpace ℝ (Fin 2)) (p q : EuclideanSpace ℝ (Fin 2)) :
    f.linearIsometryEquiv (p -ᵥ q) = f p -ᵥ f q :=
  AffineIsometryEquiv.map_vsub f p q

-- The concrete translation sends the origin to its translation vector.
example (v : EuclideanSpace ℝ (Fin 2)) :
    AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin 2)) v 0 = v := by
  change v + (0 : EuclideanSpace ℝ (Fin 2)) = v
  exact add_zero v

private theorem discrete_module_finite (L : Submodule ℤ (EuclideanSpace ℝ (Fin 2)))
    [DiscreteTopology L] : Module.Finite ℤ L :=
  instModuleFinite_of_discrete_submodule L

private theorem discrete_module_free (L : Submodule ℤ (EuclideanSpace ℝ (Fin 2)))
    [DiscreteTopology L] : Module.Free ℤ L :=
  instModuleFree_of_discrete_submodule L

private theorem lattice_rank (L : Submodule ℤ (EuclideanSpace ℝ (Fin 2)))
    [DiscreteTopology L] [IsZLattice ℝ L] : Module.finrank ℤ L = 2 := by
  simpa using ZLattice.rank ℝ L

#print axioms translated_point
#print axioms linear_part_difference
#print axioms discrete_module_finite
#print axioms discrete_module_free
#print axioms lattice_rank

end AlgebraNotesApiProbe
