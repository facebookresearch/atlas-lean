/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.LinearAlgebra.SymplecticGroup

/-! Check that the Blueprint's equation formulation is covered by the credited Mathlib theorem. -/

open Matrix

example {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R]
    {A : Matrix (l ⊕ l) (l ⊕ l) R} (hA : A * J l R * Aᵀ = J l R) : A.det = 1 :=
  SymplecticGroup.det_eq_one (SymplecticGroup.mem_iff.mpr hA)
