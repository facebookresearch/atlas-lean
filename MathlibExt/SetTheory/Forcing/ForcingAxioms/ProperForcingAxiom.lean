/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.Order.PFilter
public import Mathlib.SetTheory.Cardinal.Aleph
public import MathlibExt.SetTheory.Forcing.ForcingAxioms.Proper
public import MathlibExt.SetTheory.Tree.Aronszajn
public import MathlibExt.SetTheory.Tree.Basic
public import MathlibExt.SetTheory.Tree.Suslin

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 49, Logic 562, Logic 581

/-! ## Tier 4: no Suslin trees

A node of an `ω₁`-tree is **good** if it extends to every higher level.
Every level carries a good node, and goodness persists upward
(`good_node_at_level`, `good_above`); the engine is that predecessors meet
every level below the rank (`pred_meets_level_below_rank`), so no node can
skip a level (`reaches_level_between`).  The good nodes, forced with in
reverse tree order, forms a ccc poset in which compatibility is comparability
(`goodNodes_compat_iff`, `isCCC_goodNodes`); the level sets are dense
(`isCoinitial_goodNodes_level`), so `MA_{ℵ₁}` yields a filter meeting all
levels — an uncountable chain, contradicting Suslin
(`pfa_implies_no_suslin_tree`).
-/

open Cardinal Ordinal Set Order

/-!
# Proper Forcing Axiom; Proper Forcing Axiom theorems (part I); Proper Forcing Axioms theorems
  (part II)

## References

* Jech (for `ProperForcingAxiom`)
* 1. pred_meets_level_below_rank — predecessors meet every level below the WF-rank: if $\delta <
  \mathrm{rank}(u)$ then some $v < u$ has rank exactly $\delta$; by WF-induction unfolding
  WellFounded.rank as a sup. Source: standard fact about rank functions, original to this
  formalization. Background: rank by transfinite recursion; file docstring cites T. Jech, Set
  Theory, Lemma 6.5. 2. reaches_level_between — no node skips a level: if $v \le w$,
  $\mathrm{rank}(w) = \delta$ and $\mathrm{rank}(v) <, \gamma \le \delta$, then some $x \ge v$ has
  rank exactly $\gamma$ (the predecessor of $w$ at level $\gamma$ lies on, $v$'s branch). Source:
  direct observation, original to this formalization; background: predecessors in a tree form a
  chain. 3. good_node_at_level — every level $\delta < \omega_1$ of an $\omega_1$-tree carries a
  good node (one extending to every higher level below $\omega_1$); otherwise the countably many
  "dying levels" at level $\delta$ would be bounded below $\omega_1$. Source: the pruning argument
  for normal subtrees of $\omega_1$-trees, original to this formalization. Background: normal
  $\kappa$-trees; file docstring cites Jech, Set Theory, Ch. 9. 4. good_above — goodness persists
  upward: above a good node $t$, every level $\beta$ with $\mathrm{rank}(t) < \beta <, \omega_1$
  carries a good node above $t$. Source: the pruning argument (item 3's source). 5.
  goodNodes_le_iff — the good-node forcing order is reverse tree order, by rfl. Source: direct
  observation, original to this formalization. 6. goodNodes_compat_iff — in tree forcing,
  compatibility is comparability: $s, t$ have a common extension iff they are comparable in the
  tree. Source: standard fact about forcing with trees, original to this formalization.
  Background: forcing with trees to add a branch; file docstring cites Jech, Set Theory, Ch. 15.
  7. isCCC_goodNodes — the good-node forcing of a Suslin tree is ccc: a forcing antichain is a
  tree antichain (item 6), hence countable by the Suslin antichain clause. Source: standard;
  original to this formalization (item 6's source). 8. isCoinitial_goodNodes_level — for $\beta <
  \omega_1$, the level set (good nodes of rank $\ge \beta$) is dense in the forcing: goodness
  supplies an extension at any prescribed level. Source: standard density fact for tree forcing,
  original to this formalization; via item 4. 9. pfa_implies_no_suslin_tree — PFA implies there
  are no Suslin trees: via $\mathrm{MA}_{\aleph_1}$ (previous submission, item 12), the ccc
  good-node forcing (item 7) with dense level sets (item 8) yields a filter meeting every level —
  an uncountable chain, contradicting the Aronszajn chain clause. Sources: original, R. Solovay
  and S. Tennenbaum, "Cohen extensions and Souslin's problem", Ann. Math. 94 (1971), 201–245
  ($\mathrm{MA}$ implies Suslin's, Hypothesis); textbook, T. Jech, Set Theory, 3rd ed., Springer,
  2003, Ch. 16 (file docstring cites Theorem 16.19).
-/

namespace MetaMathlibExt

-- Logic 49: Proper Forcing Axiom

/-- The Proper Forcing Axiom: For any proper poset ℙ, any condition p∈ℙ, for any sequence (D_α :
α<ω₁) of dense subsets of ℙ, there is a filter G⊆ ℙ meeting every D_α and p∈ G.
-/
def ProperForcingAxiom : Prop :=
  ∀ (P : Type*) [PartialOrder P], IsProperForcing P →
    ∀ D : Set (Set P), (∀ S ∈ D, IsCoinitial S) → Cardinal.mk D ≤ aleph 1 →
    ∀ p : P, ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ D, (G ∩ S).Nonempty

end MetaMathlibExt

end
