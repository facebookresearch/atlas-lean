/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.InnerProductSpace.l2Space
import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook122

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook122Wanted.Tests

-- The standard Hilbert basis witnesses the infinite-dimensional hypothesis in real ℓ².
example : ∃ x : ℕ → lp (fun _ : ℕ => ℝ) 2,
    (∀ σ : Equiv.Perm ℕ, Summable (x ∘ σ)) ∧ ¬ Summable (fun n => ‖x n‖) := by
  let E := lp (fun _ : ℕ => ℝ) 2
  let b : HilbertBasis ℕ ℝ E := ⟨LinearIsometryEquiv.refl ℝ E⟩
  apply dvoretzky_rogers_unconditional_not_absolute E
  intro h
  exact Module.Finite.not_linearIndependent_of_infinite (⇑b) b.orthonormal.linearIndependent

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook122Wanted.Tests
