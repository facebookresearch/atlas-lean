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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Logic.Relation

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

/-- An instance: vertex count `n`, root, child entries `(parent, child, is right child)`, and
the width bound `K`. -/
abbrev EumorphousTreeLayoutInstance := ℕ × ℕ × List (ℕ × ℕ × Bool) × ℕ

/-- `c` is the right child (`b = true`) or the left child (`b = false`) of `p`. -/
def IsChild (i : EumorphousTreeLayoutInstance) (b : Bool) (p c : Fin i.1) : Prop :=
  ((p : ℕ), (c : ℕ), b) ∈ i.2.2.1

/-- `w` is `u` or a descendant of `u`. -/
def IsDescendant (i : EumorphousTreeLayoutInstance) (u w : Fin i.1) : Prop :=
  Relation.ReflTransGen (fun p c => ∃ b, IsChild i b p c) u w

/-- Well-formedness of an instance: the root and all entries use vertices below `n`, every
vertex is the child in at most one entry, the root in none, every vertex has at most one child
on each side, every vertex descends from the root (so the entries form a binary tree rooted
there), and `K` is positive. -/
def WellFormed (i : EumorphousTreeLayoutInstance) : Prop :=
  i.2.1 < i.1 ∧ (∀ e ∈ i.2.2.1, e.1 < i.1 ∧ e.2.1 < i.1) ∧
    (i.2.2.1.map fun e => e.2.1).Nodup ∧ (∀ e ∈ i.2.2.1, e.2.1 ≠ i.2.1) ∧
    (∀ e ∈ i.2.2.1, ∀ f ∈ i.2.2.1, e.1 = f.1 → e.2.2 = f.2.2 → e.2.1 = f.2.1) ∧
    (∀ v : Fin i.1, ∃ r : Fin i.1, (r : ℕ) = i.2.1 ∧ IsDescendant i r v) ∧
    0 < i.2.2.2

/-- `φ` maps the subtree rooted at `u` isomorphically onto the subtree rooted at `v`, as a
binary tree: `φ u = v`, and for every descendant `w` of `u` and each side, the child of `w` on
that side is sent to the child of `φ w` on the same side, and `φ w` has a child on that side
only if `w` has one. -/
def IsSubtreeIso (i : EumorphousTreeLayoutInstance) (u v : Fin i.1)
    (φ : Fin i.1 → Fin i.1) : Prop :=
  φ u = v ∧ ∀ w, IsDescendant i u w → ∀ b,
    (∀ c, IsChild i b w c → IsChild i b (φ w) (φ c)) ∧
      ((∃ c, IsChild i b (φ w) c) → ∃ c, IsChild i b w c)

/-- Some injective layout `pt` in grid points satisfies the width bound and conditions (1)-(4)
as read in the module docstring. -/
def EumorphousTreeLayoutFeasible (i : EumorphousTreeLayoutInstance) : Prop :=
  ∃ pt : Fin i.1 → ℤ × ℤ, Function.Injective pt ∧
    (∃ a : ℤ, ∀ v, a ≤ (pt v).1 ∧ (pt v).1 ≤ a + i.2.2.2) ∧
    -- (1): y-coordinate = level, vertices of one level at least two apart
    (∀ v : Fin i.1, (v : ℕ) = i.2.1 → (pt v).2 = 0) ∧
    (∀ b p c, IsChild i b p c → (pt c).2 = (pt p).2 + 1) ∧
    (∀ u v, u ≠ v → (pt u).2 = (pt v).2 → 2 ≤ |(pt u).1 - (pt v).1|) ∧
    -- (2): right child to the right, left child to the left, parent centered on both
    (∀ p c, IsChild i true p c → (pt p).1 < (pt c).1) ∧
    (∀ p c, IsChild i false p c → (pt c).1 < (pt p).1) ∧
    (∀ p l r, IsChild i false p l → IsChild i true p r →
      (pt p).1 - (pt l).1 = (pt r).1 - (pt p).1) ∧
    -- (3): straight-line edges do not cross
    (∀ b₁ b₂ p₁ c₁ p₂ c₂, IsChild i b₁ p₁ c₁ → IsChild i b₂ p₂ c₂ →
      (pt p₁).2 = (pt p₂).2 → (pt p₁).1 < (pt p₂).1 → (pt c₁).1 < (pt c₂).1) ∧
    -- (4): isomorphic subtrees have translated images
    ∀ u v φ, IsSubtreeIso i u v φ →
      ∃ d : ℤ × ℤ, ∀ w, IsDescendant i u w → pt (φ w) = pt w + d

open Classical in
/-- EUMORPHOUS TREE LAYOUT as a decision problem over bitstrings. -/
noncomputable def eumorphousTreeLayoutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EumorphousTreeLayoutInstance) x with
  | some i => decide (WellFormed i ∧ EumorphousTreeLayoutFeasible i)
  | none => false

/-- **EUMORPHOUS TREE LAYOUT is NP-complete.** Source: Johnson, NP-completeness column (1982),
problem [8]; Supowit and Reingold (1983). -/
public theorem_wanted eumorphousTreeLayout_npComplete :
    eumorphousTreeLayoutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L eumorphousTreeLayoutDec

end MetaMathlibExt.Complexity.NPComplete.EumorphousTreeLayout
