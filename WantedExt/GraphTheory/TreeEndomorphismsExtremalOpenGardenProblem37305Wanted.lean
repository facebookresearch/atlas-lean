/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Trees with the fewest and the most endomorphisms (Open Problem Garden 37305)

Open Problem Garden, Extremal problem on the number of tree endomorphism (Zhicong Lin): an
endomorphism of a graph is a map of its vertex set that preserves edges. Among all trees on `n`
vertices, the star `S_n` has the most endomorphisms and the path `P_n` the fewest.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Star

@[expose] public section

namespace MathlibExt.GraphTheory.TreeEndomorphismsExtremalOpenGardenProblem37305Wanted

/-!
Source: Open Problem Garden, Extremal problem on the number of tree endomorphism (node 37305;
Zhicong Lin),
http://www.openproblemgarden.org/op/extremal_problem_on_the_number_of_tree_endomorphism.
UnsolvedMath record UM-00003283 (`OPG-37305`), dataset ulamai/UnsolvedMath v1.8.0.

Trees on `n` vertices are taken on the vertex set `Fin n` (every tree is isomorphic to one there and
the number of endomorphisms is an isomorphism invariant), with `n ≥ 1` written `n + 1` (there is no
tree on `0` vertices). An endomorphism is a graph homomorphism `T →g T`; the path is
`SimpleGraph.pathGraph` and the star is `SimpleGraph.starGraph` centred at `0`.
-/

/-- The number of endomorphisms of a graph `G` on a finite vertex type: the graph homomorphisms
`G →g G`, maps of the vertex set that send adjacent vertices to adjacent vertices. -/
noncomputable def numEndomorphisms {V : Type} (G : SimpleGraph V) : ℕ :=
  Nat.card (G →g G)

/-- Lin's conjecture: among all trees on `n + 1` vertices (labelled by `Fin (n + 1)`), the path
`P_{n+1}` has the fewest endomorphisms and the star `S_{n+1}` (centre `0`) the most. -/
def treeEndomorphismsExtremal : Prop :=
  ∀ (n : ℕ) (T : SimpleGraph (Fin (n + 1))), T.IsTree →
    numEndomorphisms (SimpleGraph.pathGraph (n + 1)) ≤ numEndomorphisms T ∧
      numEndomorphisms T ≤ numEndomorphisms (SimpleGraph.starGraph (0 : Fin (n + 1)))

/--
Resolved true: Csikvári and Lin proved that every tree `T_n` on `n` vertices satisfies `|End(P_n)| ≤
|End(T_n)| ≤ |End(S_n)|`. Source: Open Problem Garden, Extremal problem on the number of tree
endomorphism (node 37305; Zhicong Lin),
http://www.openproblemgarden.org/op/extremal_problem_on_the_number_of_tree_endomorphism; resolution:
P. Csikvári and Z. Lin, Graph homomorphisms between trees, Electron. J. Combin. 21(4) (2014), #P4.9,
doi:10.37236/4096; arXiv:1307.6721, Theorem 1.8: for all trees T_n on n vertices, |End(P_n)| ≤
|End(T_n)| ≤ |End(S_n)|, where End(G) is the set of homomorphisms from G to itself (Section 1),
https://doi.org/10.37236/4096.
-/
public theorem_wanted treeEndomorphismsExtremal_holds : treeEndomorphismsExtremal

end MathlibExt.GraphTheory.TreeEndomorphismsExtremalOpenGardenProblem37305Wanted
