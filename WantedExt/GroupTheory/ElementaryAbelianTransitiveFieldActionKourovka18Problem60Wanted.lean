/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Transitive automorphism groups of an elementary abelian 2-group (Kourovka Notebook Problem 18.60)

Kourovka Notebook, Problem 18.60 (D. V. Lytkina), marked solved in the 21st issue: let `V` be an
infinite countable elementary abelian additive 2-group. Does `Aut V` contain a subgroup `G` such
that (a) `G` is transitive on the non-zero elements of `V`, and (b) if `H` is the stabilizer in `G`
of a non-zero `v ∈ V`, then `V = ⟨v⟩ ⊕ V_v` with `V_v` `H`-invariant, `H` is isomorphic to the
multiplicative group `P*` of a locally finite field `P` of characteristic `2`, and the action of `H`
on `V_v` is similar to the action of `P*` on `P` by multiplication? Conjecture: such a group `G`
does not exist.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Basic.Countable.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.ElementaryAbelianTransitiveFieldActionKourovka18Problem60Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.60 (D. V. Lytkina). UnsolvedMath record
UM-00701489 (`KOU-18.60`), dataset ulamai/UnsolvedMath v1.8.0.

The target is the conjecture (non-existence), quantified over every countably infinite `V` with `v +
v = 0`. `Aut V` is represented by subgroups of `Sym(V)` consisting of additive bijections.
Similarity of the actions is an isomorphism `ψ : H ≃ P*` and a bijection `θ : V_v → P` with `θ(h w)
= ψ(h) θ(w)` (any bijection, not necessarily additive: the weaker hypothesis, so the non-existence
claim is the stronger one). Such a `θ` maps the common fixed point `0` of `H` to `0` (as `P` is
infinite), so `H` is transitive on `V_v ∖ {0}`, which is what the resolving preprint uses.
-/

/-- `P` is a locally finite field: every finitely generated subfield is finite. -/
def IsLocallyFiniteField (P : Type) [Field P] : Prop :=
  ∀ s : Finset P, Finite (Subfield.closure (s : Set P))

/-- Kourovka 18.60 (D. V. Lytkina), the conjecture: for a countably infinite elementary abelian
2-group `V`, no group `G` of automorphisms of `V` (a subgroup of `Sym(V)` consisting of additive
bijections) is (a) transitive on `V ∖ {0}` and (b) such that, for every nonzero `v` with stabilizer
`H = G_v`, there are an `H`-invariant subgroup `V_v` with `V = ⟨v⟩ ⊕ V_v`, an isomorphism
`ψ : H ≃ P*` onto the multiplicative group of a locally finite field `P` of characteristic `2`,
and a bijection `θ : V_v → P` with `θ(h w) = ψ(h) θ(w)`. -/
def noTransitiveFieldLikeAutomorphismGroup : Prop :=
  ∀ (V : Type) [AddCommGroup V], Countable V → Infinite V → (∀ v : V, v + v = 0) →
    ¬ ∃ G : Subgroup (Equiv.Perm V), (∀ g ∈ G, ∀ a b : V, g (a + b) = g a + g b) ∧
      (∀ u w : V, u ≠ 0 → w ≠ 0 → ∃ g ∈ G, g u = w) ∧
      ∀ v : V, v ≠ 0 → ∃ (W : AddSubgroup V) (P : Type) (_ : Field P),
        CharP P 2 ∧ IsLocallyFiniteField P ∧ IsCompl (AddSubgroup.zmultiples v) W ∧
        (∀ g ∈ G, g v = v → ∀ w ∈ W, g w ∈ W) ∧
        ∃ (ψ : ↥(G ⊓ MulAction.stabilizer (Equiv.Perm V) v) ≃* Pˣ) (θ : V → P),
          Set.BijOn θ (W : Set V) Set.univ ∧
          ∀ h : ↥(G ⊓ MulAction.stabilizer (Equiv.Perm V) v), ∀ w ∈ W,
            θ ((h : Equiv.Perm V) w) = (ψ h : P) * θ w

/--
Resolved true: the Kourovka Notebook (21st issue) records that there are no such groups (K.
Muliarchyk, 2026). Muliarchyk's Theorem 1 excludes a group transitive on the nonzero vectors of an
`𝔽₂`-space of dimension at least `4` whose point stabilizer preserves a complement to `𝔽₂ v` and is
transitive on its nonzero vectors; a similarity with `P*` acting on `P` gives that transitivity
(Corollary 2). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.60 (D. V. Lytkina);
resolution: K. Muliarchyk, Involution centralizers and a linear obstruction: Kourovka Problems 18.59
and 18.60, preprint, 2026, Theorem 1: for an F_2-space V of dimension at least 4, no K ≤ GL(V)
transitive on V ∖ {0} has a point stabilizer preserving a complement W_v to F_2 v and transitive on
W_v ∖ {0}; Corollary 2: the nonexistence conjecture of Problem 18.60 holds; the Kourovka Notebook
(21st issue) marks 18.60 solved,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka_18_59-18_60_solution.pdf.
-/
public theorem_wanted noTransitiveFieldLikeAutomorphismGroup_holds :
    noTransitiveFieldLikeAutomorphismGroup

end MathlibExt.GroupTheory.ElementaryAbelianTransitiveFieldActionKourovka18Problem60Wanted
