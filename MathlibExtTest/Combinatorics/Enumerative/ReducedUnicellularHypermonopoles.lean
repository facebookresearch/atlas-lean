/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ReducedUnicellularHypermonopoles

open MetaMathlibExt

-- The three-cycle has no bud, including at the step from the last point to zero.
example : ∀ i, ((finRotate 3)⁻¹ * finRotate 3) i ≠ finRotate 3 i :=
  (reduced_iff_forall_face_ne_finRotate (finRotate 3)).mp (by decide)

-- Swapping 1 and 2 leaves a bud at zero, detected at its cyclic predecessor.
example : ¬ ∀ i, (Equiv.swap (1 : Fin 3) 2) i ≠ i := by
  apply (reduced_iff_forall_face_ne_finRotate _).not.mpr
  intro h
  exact h (Fin.last 2) (by decide)

-- At size zero the binomial denominator vanishes for every second argument.
example (k : ℕ) : cyclicProductNumber 0 k = 0 := by
  simp [cyclicProductNumber]
