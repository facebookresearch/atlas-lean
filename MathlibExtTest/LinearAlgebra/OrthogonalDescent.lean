/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.LinearAlgebra.Complex.Module
import MathlibExt.LinearAlgebra.OrthogonalDescent

namespace MetaMathlibExt

/-- The purely imaginary vector `(I, -I)` annihilates every real diagonal row.
Descent supplies a nonzero real vector annihilating the whole family. -/
example : ∃ u : Fin 2 → ℝ, u ≠ 0 ∧ ∀ a : ℝ, a * u 0 + a * u 1 = 0 := by
  let S := Set.range fun a : ℝ ↦ ![a, a]
  obtain ⟨u, hu, horth⟩ := exists_orthogonal_of_orthogonal_over_extension S
    ![Complex.I, -Complex.I] (Function.ne_iff.mpr ⟨0, Complex.I_ne_zero⟩) (by
      rintro _ ⟨a, rfl⟩
      simp [Fin.sum_univ_two])
  refine ⟨u, hu, fun a ↦ ?_⟩
  simpa [Fin.sum_univ_two] using horth _ ⟨a, rfl⟩

end MetaMathlibExt
