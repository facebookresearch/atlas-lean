/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all MathlibExt.Combinatorics.LocallySparseTripleSystemErdosProblem1076

/-! Regression checks for the cyclic construction and the public statement. -/

namespace MathlibExt.Combinatorics.LocallySparseTripleSystemErdosProblem1076Wanted

-- The cyclic base has 23 vertices and 92 triples.
example : Fintype.card (Vertex 0) = 23 := by decide +kernel

example : (family 0).card = 92 := by decide +kernel

-- One genuinely nontrivial affine lift has 529 vertices and 48,668 triples.
example : ∃ E : Finset (Finset (Fin 529)), SetFamily.IsUniform E 3 ∧
    ¬ SetFamily.ContainsSubgraph E 5 3 ∧ E.card = 48668 :=
  exists_family 1

-- The two triples on each side share their two noncentral vertices.
example : (coreTriple 0 ∩ coreTriple 1).card = 2 ∧
    (coreTriple 2 ∩ coreTriple 3).card = 2 := by decide +kernel

-- The central pair is reserved: it belongs to the support and to none of the four triples.
example : (0, 1) ∈ support ∧ ∀ i : Fin 4, ¬ (0 ∈ coreTriple i ∧ 1 ∈ coreTriple i) := by
  decide +kernel

example : ¬ singleFamilyAsymptotic := singleFamilyAsymptotic_refuted

end MathlibExt.Combinatorics.LocallySparseTripleSystemErdosProblem1076Wanted
