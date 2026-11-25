/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Antichain
public import Domains.Biology.PopulationGenetics.AdmixtureGraph
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The cut lemma for admixture-graph lineage visit weights

Soraggi and Wiuf's general admixture graphs allow a node to have any finite
set of parents, with edge proportions summing to `1`. Atlas's current
`AdmixtureGraph` restricts non-root nodes to one or two parents. The cut lemma
below is stated directly for an abstract finite parent relation and a
`visit` function satisfying the same first-step recursion as
`AdmixtureGraph.visit`; it therefore does not use the one-or-two-parent
restriction.

If an antichain `S` meets every root-ward parent chain from `X` to the root,
then the visit weights of the nodes of `S` from `X` sum to `1`; for nonnegative
proportions they are the probabilities that the lineage of `X` visits these
nodes. The singleton cut `{root}` is the existing statement that every lineage
reaches the root.

This file does not introduce a generalized graph structure. It supplies the
parent-relation core and its specialization to the current
`AdmixtureGraph`.

## Main results

* `Admixture.sum_visit_eq_one_of_isAntichain_of_separates`: the cut lemma for
  abstract parent data.
* `AdmixtureGraph.sum_visit_cut_eq_one`: the cut lemma for an Atlas
  admixture graph.

## References

* S. Soraggi and C. Wiuf, *General theory for stochastic admixture graphs and
  F-statistics*, Theoretical Population Biology 125 (2019), 56–66.
* N. Patterson et al., *Ancient admixture in human history*, Genetics 192
  (2012), 1065–1093, Appendix.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Admixture

private theorem visit_eq_zero_of_ne_of_not_transGen {V : Type*} [DecidableEq V]
    (parents : V → Finset V) (prop : V → V → ℝ) (visit : V → V → ℝ)
    (wf : WellFounded fun Y X => Y ∈ parents X)
    (visit_eq : ∀ X c,
      visit X c = if X = c then 1 else ∑ Y ∈ parents X, prop X Y * visit Y c)
    (X c : V) (hne : X ≠ c)
    (hnot : ¬ Relation.TransGen (fun Y X => Y ∈ parents X) c X) :
    visit X c = 0 := by
  suffices h : ∀ Z, Z ≠ c → ¬ Relation.TransGen (fun Y X => Y ∈ parents X) c Z → visit Z c = 0
    from h X hne hnot
  intro Z
  refine wf.induction
    (C := fun Z => Z ≠ c → ¬ Relation.TransGen (fun Y X => Y ∈ parents X) c Z → visit Z c = 0)
    Z ?_
  intro X ih hne hnot
  rw [visit_eq X c]
  simp only [hne, ↓reduceIte]
  apply Finset.sum_eq_zero
  intro Y hYmem
  have hYne : Y ≠ c := by
    intro heq
    apply hnot
    have hmem : (fun Y X => Y ∈ parents X) c X := heq ▸ hYmem
    exact Relation.TransGen.single hmem
  have hYnot : ¬ Relation.TransGen (fun Y X => Y ∈ parents X) c Y := by
    intro htrans
    apply hnot
    exact htrans.tail hYmem
  rw [ih Y hYmem hYne hYnot, mul_zero]

/-- **Cut lemma for signed lineage visit weights**.

Let `parents X` be the (finite, possibly more than two) parents of node `X`, with well-founded
parent relation, and let `prop X Y` be real weights (no sign condition is needed), such as
admixture proportions, summing to `1` over the parents of every non-root node. Let the visit
weights `visit X c` satisfy the first-step equation
`visit X c = 1` if `X = c`, else `∑ Y ∈ parents X, prop X Y * visit Y c`
(for nonnegative `prop` and a root without parents, the equation of the probability that the
lineage of `X`, traced toward the root, passes through `c`).

If `S` is an antichain for the ancestor relation (no element of `S` is a proper ancestor of
another) and `S` separates `X` from `root` (every root-ward parent chain from `X` to `root` meets
`S`), then the visit weights of `X` across the cut sum to `1`. With signed `prop` they need not be
probabilities: parent weights `2` and `-1`, each parent a child of the root, give visit weights
`2` and `-1` on the cut formed by the two parents. -/
theorem sum_visit_eq_one_of_isAntichain_of_separates {V : Type*} [DecidableEq V]
    (root : V) (parents : V → Finset V) (prop : V → V → ℝ) (visit : V → V → ℝ)
    (wf : WellFounded fun Y X => Y ∈ parents X)
    (sum_prop : ∀ X, X ≠ root → ∑ Y ∈ parents X, prop X Y = 1)
    (visit_eq : ∀ X c,
      visit X c = if X = c then 1 else ∑ Y ∈ parents X, prop X Y * visit Y c)
    (S : Finset V) (X : V)
    (hanti : IsAntichain (Relation.TransGen fun Y X => Y ∈ parents X) (S : Set V))
    (hsep : ∀ π : List V, π.head? = some X → π.getLast? = some root →
      π.IsChain (fun a b => b ∈ parents a) → ∃ c ∈ S, c ∈ π) :
    ∑ c ∈ S, visit X c = 1 := by
  suffices h : ∀ Z, (∀ π : List V, π.head? = some Z → π.getLast? = some root →
      π.IsChain (fun a b => b ∈ parents a) → ∃ c ∈ S, c ∈ π) → ∑ c ∈ S, visit Z c = 1
    from h X hsep
  intro Z
  refine wf.induction (C := fun Z => (∀ π : List V, π.head? = some Z → π.getLast? = some root →
      π.IsChain (fun a b => b ∈ parents a) → ∃ c ∈ S, c ∈ π) → ∑ c ∈ S, visit Z c = 1) Z ?_
  intro X ih hsep
  by_cases hX : X ∈ S
  · trans visit X X
    · apply Finset.sum_eq_single X
      · intro c hc hne
        apply visit_eq_zero_of_ne_of_not_transGen parents prop visit wf visit_eq X c
        · exact hne.symm
        · intro htrans
          have heq : c = X := hanti.eq (Finset.mem_coe.mpr hc) (Finset.mem_coe.mpr hX) htrans
          exact hne heq
      · intro hcon
        exact absurd hX hcon
    · rw [visit_eq X X]
      simp only [↓reduceIte]
  · have hXne : X ≠ root := by
      intro heq
      obtain ⟨c, hcS, hcmem⟩ := hsep [X] rfl (by simp [heq]) (List.isChain_singleton X)
      rw [List.mem_singleton] at hcmem
      subst hcmem
      exact hX hcS
    have hexpand : ∀ c ∈ S, visit X c = ∑ Y ∈ parents X, prop X Y * visit Y c := by
      intro c hc
      have hne : X ≠ c := fun heq => hX (heq ▸ hc)
      rw [visit_eq X c]
      simp only [hne, ↓reduceIte]
    calc ∑ c ∈ S, visit X c
        = ∑ c ∈ S, ∑ Y ∈ parents X, prop X Y * visit Y c :=
          Finset.sum_congr rfl hexpand
      _ = ∑ Y ∈ parents X, ∑ c ∈ S, prop X Y * visit Y c :=
          Finset.sum_comm
      _ = ∑ Y ∈ parents X, prop X Y * (∑ c ∈ S, visit Y c) := by
          apply Finset.sum_congr rfl
          intro Y hY
          rw [← Finset.mul_sum]
      _ = ∑ Y ∈ parents X, prop X Y * 1 := by
          apply Finset.sum_congr rfl
          intro Y hYmem
          congr 1
          apply ih Y hYmem
          intro π hhead hlast hchain
          cases π with
          | nil => simp at hhead
          | cons hd tl =>
            have hhd : hd = Y := Option.some.inj hhead
            subst hhd
            obtain ⟨c, hcS, hcmem⟩ := hsep (X :: hd :: tl) rfl (by simpa using hlast)
              (List.isChain_cons_cons.mpr ⟨hYmem, hchain⟩)
            rw [List.mem_cons] at hcmem
            rcases hcmem with rfl | hmem
            · exact absurd hcS hX
            · exact ⟨c, hcS, hmem⟩
      _ = ∑ Y ∈ parents X, prop X Y := by simp
      _ = 1 := sum_prop X hXne

end MathlibExt.Biology.PopulationGenetics.Admixture

namespace MathlibExt.Biology.PopulationGenetics.AdmixtureGraph

/-- The cut lemma for an admixture graph: if the antichain `S` meets every
root-ward parent chain from `X` to the root, then the visit weights of the nodes
of `S` from `X` sum to `1`; as admixture proportions are nonnegative, these are
the probabilities that the lineage of `X` visits the nodes of `S`. -/
theorem sum_visit_cut_eq_one {V : Type*} [DecidableEq V]
    (G : AdmixtureGraph V) (S : Finset V) (X : V)
    (hanti : IsAntichain (Relation.TransGen fun Y X => Y ∈ G.parents X) (S : Set V))
    (hsep : ∀ π : List V, π.head? = some X → π.getLast? = some G.root →
      π.IsChain (fun a b => b ∈ G.parents a) → ∃ c ∈ S, c ∈ π) :
    ∑ c ∈ S, G.visit X c = 1 :=
  Admixture.sum_visit_eq_one_of_isAntichain_of_separates G.root G.parents G.prop G.visit G.wf
    G.sum_prop G.visit_eq S X hanti hsep

end MathlibExt.Biology.PopulationGenetics.AdmixtureGraph
