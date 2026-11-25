/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.Percolation.BurtonKeane.FiniteModification

/-! # Changing a single edge of a configuration -/

open StatMech
open MathlibExt.Probability.Percolation.BurtonKeaneWanted

example (e f : Sym2 (Lattice.Site 2)) (h : e ≠ f) (ω : ConfigSpace (Sym2 (Lattice.Site 2))) :
    let η : ConfigSpace ↥({e} : Finset _) := fun _ => false
    setPattern {e} η ω e = false ∧ setPattern {e} η ω f = ω f := by
  dsimp only
  exact ⟨setPattern_of_mem _ (Finset.mem_singleton_self _) _,
    setPattern_of_not_mem _ (by simpa using h.symm) _⟩
