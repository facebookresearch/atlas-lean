/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FiniteStateConjugacyProblem

/-! # Compatibility of the conjugacy problem with the finite-state subgroup -/

namespace MathlibExtTest.GroupTheory.FiniteStateConjugacyProblem

open MathlibExt.GroupTheory
open FiniteStateConjugacyProblemKourovka16Problem34Wanted

example {d : ℕ} (g : Equiv.Perm (List (Fin d))) :
    g ∈ FiniteStateTree.finiteStateAutomorphisms d ↔ IsFiniteStateAut g :=
  FiniteStateTree.mem_finiteStateAutomorphisms_iff g

example {d : ℕ} (g : Equiv.Perm (List (Fin d))) (v : List (Fin d)) :
    treeSection g v = FiniteStateTree.treeSection g v := rfl

end MathlibExtTest.GroupTheory.FiniteStateConjugacyProblem
