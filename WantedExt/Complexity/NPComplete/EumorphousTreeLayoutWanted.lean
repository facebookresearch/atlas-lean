/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EUMORPHOUS TREE LAYOUT is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide" (second edition), Journal of
Algorithms 3 (1982), 89-99, doi:10.1016/0196-6774(82)90011-6, problem [8] EUMORPHOUS TREE
LAYOUT (reference: Supowit and Reingold; transformation from 3SAT);
K. J. Supowit and E. M. Reingold, "The complexity of drawing trees nicely", Acta Informatica 18
(1983), 377-392, doi:10.1007/BF00289576.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EumorphousTreeLayoutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EumorphousTreeLayout

/-!
# EUMORPHOUS TREE LAYOUT is NP-complete

INSTANCE: a rooted binary tree `T = (V, E)` and a positive integer `K`. QUESTION: is there an
assignment of the vertices of `T` to distinct grid points so that all can be enclosed within a
rectangle of width `K` or less, and the following properties are satisfied?

1. All vertices with level `i` in `T` have `i` as their y-coordinate, and must be at least two
   units apart.
2. A right child is to the right of its parent and a left child is to the left of its parent,
   with the parent centered on both if it has both.
3. If the edges of `T` are drawn as straight lines, no two cross each other.
4. If `T₁` and `T₂` are isomorphic subtrees of `T`, then their images in the embedding are
   identical (up to translation).

The tree has vertices `0, ..., n - 1`, a root, and a list of entries `(p, c, b)`: `c` is the
left child (`b = false`) or the right child (`b = true`) of `p`. `WellFormed` makes this a
rooted binary tree: every vertex has at most one parent, the root has none, every vertex has at
most one left and at most one right child, and every vertex descends from the root.

Reading of the conditions:

* Grid points are points of `ℤ × ℤ`, the layout is `pt : Fin n → ℤ × ℤ`, and "distinct" is
  injectivity. "Enclosed within a rectangle of width `K` or less" bounds the x-coordinates to an
  interval `[a, a + K]`; the height is unconstrained.
* (1) The level of a vertex is its depth: the root has level 0 and a child has its parent's
  level plus one, so (1)'s first clause is "the root has y-coordinate 0 and every child lies one
  unit above its parent". Any other numbering of levels (e.g. from 1) is a vertical translation
  and changes no answer. "At least two units apart" for distinct vertices of one level is
  `2 ≤ |x - x'|`.
* (3) Under (1), every edge joins a vertex on level `j` to one on level `j + 1`. Two edges
  whose parents lie on different levels meet at most in a shared endpoint, two edges with a
  common parent meet only there (their other ends are distinct points of one level), and two
  edges with distinct parents `p₁, p₂` on one level have distinct children `c₁, c₂` (each
  vertex has one parent) on the next level, so the straight segments cross exactly when the
  order is reversed: `x(p₁) < x(p₂)` but `x(c₂) < x(c₁)` (x-coordinates on one level are
  distinct by (1)). Condition (3) is therefore stated as "parents on one level ordered by `x`
  have their children in the same order".
* (4) A subtree is a vertex together with all its descendants. Isomorphic subtrees are
  isomorphic as binary trees, left and right children distinguished (`IsSubtreeIso`): with
  (2), mirror-image subtrees can never have translated images, so an isomorphism forgetting
  sides would make every tree containing a non-symmetric subtree and its mirror image a
  no-instance. The isomorphism between two subtrees is unique when it exists, and "identical
  up to translation" means that it moves every vertex by one common vector `d ∈ ℤ × ℤ`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EUMORPHOUS TREE LAYOUT is NP-complete.** Source: Johnson, NP-completeness column (1982),
problem [8]; Supowit and Reingold (1983). -/
public theorem_wanted eumorphousTreeLayout_npComplete :
    eumorphousTreeLayoutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L eumorphousTreeLayoutDec

end MetaMathlibExt.Complexity.NPComplete.EumorphousTreeLayout
