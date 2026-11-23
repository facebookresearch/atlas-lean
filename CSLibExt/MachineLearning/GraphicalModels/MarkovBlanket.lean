/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.GlobalMarkov

/-!
# Markov blankets and the local Markov property of Bayesian networks

For a Bayesian network (`BayesNet`, nodes in a topological order), the **Markov blanket** of a
node `i` is the set of its parents, its children and the other parents of its children
(Pearl 1988, §3.2.1). Given its blanket, a node is conditionally independent of every other
node; given its parents, it is conditionally independent of its non-descendants (the **local
Markov property**, Lauritzen 1996, §3.2.2; Koller & Friedman 2009, Definition 3.1).

Both are graph lemmas (d-separation, `BayesNet.DSeparated`) followed by the global Markov
property `BayesNet.condIndep_of_dSeparated`. The conditional-independence corollaries keep
that theorem's `Nonempty α` instance. Conditional independence is
`MetaMathlibExt.FiniteWeight.CondIndep`, the cross-multiplied form, so no positivity of the
conditioning events is assumed.

## Main definitions

* `BayesNet.markovBlanket b i`: parents, children and co-parents of `i`, without `i`.

## Main results

* `BayesNet.dSeparated_markovBlanket`: the blanket d-separates `i` from all other nodes.
* `BayesNet.condIndep_markovBlanket`: `X i ⫫ X_rest | X_{MB(i)}`.
* `BayesNet.dSeparated_localMarkov`: the parents d-separate `i` from its non-descendants.
* `BayesNet.condIndep_localMarkov`: `X i ⫫ X_{ND(i) \ pa(i)} | X_{pa(i)}`.

## References

* J. Pearl, *Probabilistic Reasoning in Intelligent Systems*, Morgan Kaufmann (1988), §3.2.1.
* S. L. Lauritzen, *Graphical Models*, Oxford University Press (1996), §3.2.2.
* D. Koller and N. Friedman, *Probabilistic Graphical Models*, MIT Press (2009), §3.2.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset MetaMathlibExt.FiniteWeight

variable {α : Type*}

namespace BayesNet

variable {n : ℕ} (b : BayesNet α n)

theorem Edge.lt {i j : Fin n} (h : b.Edge i j) : i < j :=
  h.1

theorem Edge.not_edge {i j : Fin n} (h : b.Edge i j) : ¬ b.Edge j i := fun h' =>
  lt_asymm (h.lt b) (h'.lt b)

theorem IsDescendant.le {i j : Fin n} (h : b.IsDescendant i j) : i ≤ j := by
  induction h with
  | refl => exact le_rfl
  | tail _ hst ih => exact ih.trans (hst.lt b).le

/-- The **Markov blanket** of node `i`: its parents, its children and the other parents of its
children, excluding `i` itself. -/
def markovBlanket (i : Fin n) : Finset (Fin n) :=
  univ.filter fun j => j ≠ i ∧ (b.Edge j i ∨ b.Edge i j ∨ ∃ c, b.Edge i c ∧ b.Edge j c)

theorem mem_markovBlanket {i j : Fin n} :
    j ∈ b.markovBlanket i ↔
      j ≠ i ∧ (b.Edge j i ∨ b.Edge i j ∨ ∃ c, b.Edge i c ∧ b.Edge j c) := by
  simp [markovBlanket]

theorem not_mem_markovBlanket_self (i : Fin n) : i ∉ b.markovBlanket i := by
  simp [mem_markovBlanket]

/-- **The Markov blanket d-separates a node from all other nodes**: every path from `i` to a
node outside `{i} ∪ MB(i)` is blocked by `MB(i)`. -/
theorem dSeparated_markovBlanket (i : Fin n) :
    b.DSeparated {i} ↑(univ \ insert i (b.markovBlanket i)) ↑(b.markovBlanket i) := by
  intro x hx y hy p hp
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  simp only [coe_sdiff, coe_insert, coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_insert_iff,
    mem_coe, true_and, not_or] at hy
  obtain ⟨hyx, hyB⟩ := hy
  obtain ⟨hnd, hch, hh, hlast⟩ := hp
  match p, hnd, hch, hh, hlast with
  | [], _, _, hh, _ => exact absurd hh (by simp)
  | [a], _, _, hh, hlast =>
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at hh hlast
    exact absurd (hh ▸ hlast).symm hyx
  | [a, v], _, hch, hh, hlast =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hlast
    subst hh hlast
    have hadj : b.Adj a v := (List.isChain_cons_cons.1 hch).1
    exact absurd ((b.mem_markovBlanket).2 ⟨hyx, hadj.elim (fun h => Or.inr (Or.inl h))
      (fun h => Or.inl h)⟩) hyB
  | a :: v :: w :: rest, hnd, hch, hh, hlast =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    have hadj : b.Adj a v := (List.isChain_cons_cons.1 hch).1
    have hva : v ≠ a := fun h => by simp [h] at hnd
    have hwa : w ≠ a := fun h => by simp [h] at hnd
    rcases hadj with hav | hva'
    · by_cases hwv : b.Edge w v
      · -- `v` is a collider `a → v ← w`: then `w` is a co-parent, so the path goes on past `w`.
        have hwB : w ∈ b.markovBlanket a :=
          (b.mem_markovBlanket).2 ⟨hwa, Or.inr (Or.inr ⟨v, hav, hwv⟩)⟩
        match rest, hch, hlast with
        | [], _, hlast =>
          simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq]
            at hlast
          exact absurd (hlast ▸ hwB) hyB
        | u :: rest', _, _ =>
          refine ⟨1, by simp, Or.inr ⟨fun h => (hwv.not_edge b) h.1, ?_⟩⟩
          exact mem_coe.2 hwB
      · refine ⟨0, by simp, Or.inr ⟨fun h => hwv h.2, ?_⟩⟩
        exact mem_coe.2 ((b.mem_markovBlanket).2 ⟨hva, Or.inr (Or.inl hav)⟩)
    · refine ⟨0, by simp, Or.inr ⟨fun h => (hva'.not_edge b) h.1, ?_⟩⟩
      exact mem_coe.2 ((b.mem_markovBlanket).2 ⟨hva, Or.inl hva'⟩)

/-- **Conditional independence given the Markov blanket**: under the joint law of a Bayesian
network, node `i` is conditionally independent of all nodes outside `{i} ∪ MB(i)` given its
Markov blanket `MB(i)`. -/
theorem condIndep_markovBlanket [Fintype α] [Nonempty α] (i : Fin n) :
    CondIndep b.joint {i} ↑(univ \ insert i (b.markovBlanket i)) ↑(b.markovBlanket i) :=
  b.condIndep_of_dSeparated (b.dSeparated_markovBlanket i)

/-- Along a path that leaves `i`'s descendants only through colliders, starting with an edge
`u → m` into a descendant `m` of `i` and blocked nowhere by the parents of `i`, every node is
a descendant of `i`. -/
private lemma isDescendant_of_forward (i : Fin n) :
    ∀ (q : List (Fin n)) (u m : Fin n), b.IsDescendant i m → b.Edge u m →
      (u :: m :: q).IsChain b.Adj →
      (∀ (k : ℕ) (h : k + 2 < (u :: m :: q).length),
        ¬ b.BlockedAt {j | b.Edge j i} (u :: m :: q)[k] (u :: m :: q)[k + 1]
          (u :: m :: q)[k + 2]) →
      ∀ y, (m :: q).getLast? = some y → b.IsDescendant i y
  | [], u, m, hm, _, _, _, y, hy => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hy
    exact hy ▸ hm
  | w :: q, u, m, hm, hum, hch, hnb, y, hy => by
    have hmw : b.Adj m w := (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hch).2).1
    rcases hmw with hmw | hwm
    · refine isDescendant_of_forward i q m w (hm.tail hmw) hmw
        (List.isChain_cons_cons.1 hch).2 (fun k hk => ?_) y (by simpa using hy)
      have := hnb (k + 1) (by simp at hk ⊢; omega)
      simpa using this
    · -- `m` is a collider `u → m ← w`; unblocked means a descendant of `m` is a parent of `i`,
      -- which would close a directed cycle through `i`.
      exfalso
      refine hnb 0 (by simp) (Or.inl ⟨hum, hwm, fun d hd hdZ => ?_⟩)
      have hid : b.IsDescendant i d := hm.trans hd
      exact absurd (hid.le b) (not_le.2 (Edge.lt b hdZ))

/-- **The parents of a node d-separate it from its non-descendants** (other than its
parents). -/
theorem dSeparated_localMarkov (i : Fin n) :
    b.DSeparated {i} {j | ¬ b.IsDescendant i j ∧ ¬ b.Edge j i} {j | b.Edge j i} := by
  intro x hx y hy p hp
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  obtain ⟨hyd, hypa⟩ := hy
  obtain ⟨hnd, hch, hh, hlast⟩ := hp
  match p, hnd, hch, hh, hlast with
  | [], _, _, hh, _ => exact absurd hh (by simp)
  | [a], _, _, hh, hlast =>
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at hh hlast
    exact absurd (hlast ▸ hh ▸ Relation.ReflTransGen.refl) hyd
  | a :: v :: rest, hnd, hch, hh, hlast =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    have hadj : b.Adj a v := (List.isChain_cons_cons.1 hch).1
    rcases hadj with hav | hva
    · by_contra hnb
      simp only [PathBlocked, not_exists] at hnb
      exact hyd (b.isDescendant_of_forward a rest a v (Relation.ReflTransGen.single hav) hav hch
        hnb y (by simpa using hlast))
    · match rest, hch, hlast with
      | [], _, hlast =>
        simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq]
          at hlast
        exact absurd (hlast ▸ hva) hypa
      | w :: rest', _, _ =>
        exact ⟨0, by simp, Or.inr ⟨fun h => (hva.not_edge b) h.1, hva⟩⟩

/-- **The local Markov property**: under the joint law of a Bayesian network, node `i` is
conditionally independent of its non-descendants (other than its parents) given its
parents. -/
theorem condIndep_localMarkov [Fintype α] [Nonempty α] (i : Fin n) :
    CondIndep b.joint {i} {j | ¬ b.IsDescendant i j ∧ ¬ b.Edge j i} {j | b.Edge j i} :=
  b.condIndep_of_dSeparated (b.dSeparated_localMarkov i)

end BayesNet

end Cslib.MachineLearning.GraphicalModels
