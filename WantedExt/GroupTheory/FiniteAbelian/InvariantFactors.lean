/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.InvariantFactors

/-!
# Invariant-factor existence (compatibility import)

The declarations `AddCommGroup.elementary_divisors_equiv_invariant_factors`
and `AddCommGroup.equiv_free_prod_directSum_invariant_factors` are proved in
`MathlibExt.GroupTheory.InvariantFactors`, re-exported here for existing imports.
They preserve the statement ports of `AbelianGroups.elementary_divisors_to_invariant_factors`
and `AbelianGroups.fundamental_theorem_fg_abelian_groups_invariant_factors`
from `v1/Atlas/AlgebraNotes/code/AbelianGroups.lean` at ATLAS commit
`8de8f74fa5760eb8b768a9804494ca2ab631cf87`, lines 27–42.
The original formalization, copyright and license provenance remain in `v1/`
(with license text at `v1/LICENSE`). Only the existence and divisibility clauses
encoded in that Lean source are retained; no uniqueness claim or printed-source
fidelity is asserted here. No deferred declaration remains in this module.
-/
