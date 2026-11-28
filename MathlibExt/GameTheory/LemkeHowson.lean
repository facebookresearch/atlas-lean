/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import MathlibExt.Analysis.Convex.StdSimplexWeights

/-! # Bimatrix games and the Lemke–Howson algorithm

A bimatrix game is a two-player game in strategic form given by two payoff matrices `A` and
`B` indexed by the pure strategies `M` of player 1 (rows) and `N` of player 2 (columns); both
players maximise. Mixed strategies are probability vectors (`Convexity.StdSimplex ℝ M` and
`Convexity.StdSimplex ℝ N`), and the expected payoffs of `(x, y)` are `xᵀAy` and `xᵀBy`.

The Lemke–Howson algorithm follows a path of "almost completely labelled" vertex pairs of the
two best-response polytopes, starting from the artificial equilibrium `(0, 0)`. For a
nondegenerate game these pairs and the edges joining them form a graph in which every vertex
has degree `1` or `2`; its degree-`1` vertices are the artificial equilibrium and the Nash
equilibria. A finite graph has an even number of path endpoints, so a nondegenerate bimatrix
game has an *odd* number of Nash equilibria. This is the parity argument that Papadimitriou
abstracted into the class PPAD (Papadimitriou, *Algorithmic Game Theory*, Chapter 2,
Section 2.4).

The main result, `odd_ncard_isBimatrixNash`, proves this; the combinatorics of the
best-response polytopes it needs is developed below. Existence of an equilibrium for every
bimatrix game is the two-player case of Nash's theorem, proved from Brouwer's theorem as
`MathlibExt.GameTheory.MixedNashExistence.exists_isMixedNash`.

## Main definitions and results

* `bilinPayoff`, `IsBimatrixNash`: the expected payoffs and the Nash equilibria of the bimatrix
  game `(A, B)`.
* `bestResponses₁`, `bestResponses₂`, `IsNondegenerate`: pure best responses and
  nondegenerate games.
* `odd_ncard_isBimatrixNash`: a nondegenerate bimatrix game with nonempty strategy sets has
  finitely many Nash equilibria, and an odd number of them.

## Proof outline

* Adding a constant to all payoffs changes neither the equilibria nor the best responses, so
  all payoffs may be assumed positive.
* For a matrix `C : ι → κ → ℝ` with positive entries, the polytope
  `{x : ι → ℝ | 0 ≤ x, xᵀC ≤ 1}` is bounded. The labels of a point are the indices in `ι ⊕ κ`
  of its tight inequalities. Player 1's best response polytope is the one for `C = B` and
  player 2's the one for `C = Aᵀ`, with labels in `M ⊕ N` (respectively `N ⊕ M`).
  Nondegeneracy says that no point has more labels than the dimension `card ι`; a point with
  exactly `card ι` labels is a vertex.
* Pivoting (ratio test and rank–nullity): a vertex is determined by its labels, and dropping
  one of its labels leads along an edge to exactly one other vertex that keeps the other labels.
* Parity: fix a label `k₀`. The pairs of vertex label sets of the two polytopes that cover all
  labels except possibly `k₀`, joined by pivoting steps, form a graph in which a pair has odd
  degree exactly when it covers all labels. By the handshake lemma
  (`SimpleGraph.even_card_odd_degree_vertices`) the number of completely labelled pairs is even.
* The completely labelled pairs other than the artificial one, `(0, 0)`, correspond
  bijectively to the Nash equilibria, by normalising the two vectors and the best response
  condition. Hence the number of equilibria is odd.

All auxiliary declarations are private to this file.

## References

* C. E. Lemke, J. T. Howson, Jr., "Equilibrium points of bimatrix games", J. SIAM 12 (1964),
  413–423.
* B. von Stengel, "Equilibrium computation for two-player games in strategic and extensive
  form", Chapter 3 of *Algorithmic Game Theory* (Nisan, Roughgarden, Tardos, Vazirani eds.),
  Cambridge University Press 2007: Definition 3.2 (nondegenerate game), Algorithm 3.6
  (Lemke–Howson), Corollary 3.7 (odd number of equilibria).
* C. H. Papadimitriou, "The complexity of finding Nash equilibria", Chapter 2 of the same book,
  Sections 2.3–2.4.
-/

@[expose] public section

namespace MathlibExt.GameTheory.LemkeHowsonWanted

open Convexity

variable {M N : Type*} [Fintype M] [Fintype N]

/-- **Expected payoffs in a bimatrix game.** The expected value `xᵀCy = ∑ᵢ ∑ⱼ xᵢ Cᵢⱼ yⱼ` of the
payoff matrix `C` when player 1 plays the mixed strategy `x` and player 2 independently plays
`y` (von Stengel, *Algorithmic Game Theory*, Section 3.2). -/
noncomputable def bilinPayoff (C : M → N → ℝ) (x : StdSimplex ℝ M) (y : StdSimplex ℝ N) : ℝ :=
  ∑ i, ∑ j, x.weights i * C i j * y.weights j

/-- **Nash equilibrium of a bimatrix game.** The mixed pair `(x, y)` is a Nash equilibrium of
the game `(A, B)` if `x` maximises player 1's expected payoff `x'ᵀAy` against `y` and `y`
maximises player 2's expected payoff `xᵀBy'` against `x` (von Stengel, *Algorithmic Game
Theory*, Section 3.2). -/
def IsBimatrixNash (A B : M → N → ℝ) (x : StdSimplex ℝ M) (y : StdSimplex ℝ N) : Prop :=
  (∀ x' : StdSimplex ℝ M, bilinPayoff A x' y ≤ bilinPayoff A x y) ∧
    ∀ y' : StdSimplex ℝ N, bilinPayoff B x y' ≤ bilinPayoff B x y

/-- **Pure best responses of player 1.** The rows `i` that maximise `(Ay)ᵢ = ∑ⱼ Aᵢⱼ yⱼ`
against the mixed strategy `y` of player 2. -/
noncomputable def bestResponses₁ (A : M → N → ℝ) (y : StdSimplex ℝ N) : Finset M := by
  classical
  exact Finset.univ.filter fun i => ∀ i', ∑ j, A i' j * y.weights j ≤ ∑ j, A i j * y.weights j

/-- **Pure best responses of player 2.** The columns `j` that maximise `(xᵀB)ⱼ = ∑ᵢ xᵢ Bᵢⱼ`
against the mixed strategy `x` of player 1. -/
noncomputable def bestResponses₂ (B : M → N → ℝ) (x : StdSimplex ℝ M) : Finset N := by
  classical
  exact Finset.univ.filter fun j => ∀ j', ∑ i, x.weights i * B i j' ≤ ∑ i, x.weights i * B i j

/-- **Nondegenerate bimatrix game.** No mixed strategy with support of size `k` has more than
`k` pure best responses, for either player (von Stengel, *Algorithmic Game Theory*,
Definition 3.2). -/
def IsNondegenerate (A B : M → N → ℝ) : Prop :=
  (∀ x : StdSimplex ℝ M, (bestResponses₂ B x).card ≤ x.weights.support.card) ∧
    ∀ y : StdSimplex ℝ N, (bestResponses₁ A y).card ≤ y.weights.support.card

open Finset

section Parity

variable {L : Type*} [DecidableEq L]

/-- A family `V` of label sets has the pivoting property if dropping any label `c` of a member
`S` leads to exactly one other member containing the remaining labels of `S`. -/
private def HasPivot (V : Finset L → Prop) : Prop :=
  ∀ S, V S → ∀ c ∈ S, ∃! S', V S' ∧ c ∉ S' ∧ S.erase c ⊆ S'

/-- The member reached from `S` by dropping `c` (junk value `S` if there is none). -/
private noncomputable def piv (V : Finset L → Prop) (S : Finset L) (c : L) : Finset L := by
  classical
  exact if h : ∃ S', V S' ∧ c ∉ S' ∧ S.erase c ⊆ S' then h.choose else S

private lemma piv_spec {V : Finset L → Prop} (hV : HasPivot V) {S : Finset L} (hS : V S)
    {c : L} (hc : c ∈ S) : V (piv V S c) ∧ c ∉ piv V S c ∧ S.erase c ⊆ piv V S c := by
  have h : ∃ S', V S' ∧ c ∉ S' ∧ S.erase c ⊆ S' := (hV S hS c hc).exists
  simp only [piv, dite_eq_left h]
  exact h.choose_spec

private lemma eq_piv {V : Finset L → Prop} (hV : HasPivot V) {S : Finset L} (hS : V S)
    {c : L} (hc : c ∈ S) {S' : Finset L} (h : V S' ∧ c ∉ S' ∧ S.erase c ⊆ S') :
    S' = piv V S c :=
  (hV S hS c hc).unique h (piv_spec hV hS hc)

/-- Pivoting is reversible: if `S'` is reached from `S` by dropping `c`, then `S` is reached
from `S'` by dropping the label that entered. -/
private lemma exists_back {V : Finset L → Prop} {m : ℕ} (hV : ∀ S, V S → S.card = m)
    {S S' : Finset L} (hS : V S) (hS' : V S') {c : L} (hc : c ∈ S) (hc' : c ∉ S')
    (hsub : S.erase c ⊆ S') : ∃ c' ∈ S', c' ∉ S ∧ S'.erase c' ⊆ S := by
  have hm : 0 < m := hV S hS ▸ card_pos.2 ⟨c, hc⟩
  have hcard : (S' \ S.erase c).card = 1 := by
    rw [card_sdiff_of_subset hsub, hV S' hS', card_erase_of_mem hc, hV S hS]
    omega
  obtain ⟨c', hc'eq⟩ := card_eq_one.1 hcard
  have hc'mem : c' ∈ S' \ S.erase c := hc'eq ▸ mem_singleton_self c'
  rw [mem_sdiff] at hc'mem
  refine ⟨c', hc'mem.1, fun h => hc'mem.2 (mem_erase.2 ⟨?_, h⟩), fun l hl => ?_⟩
  · rintro rfl
    exact hc' hc'mem.1
  · rw [mem_erase] at hl
    by_contra hlS
    have : l ∈ S' \ S.erase c := mem_sdiff.2 ⟨hl.2, fun h => hlS (mem_of_mem_erase h)⟩
    rw [hc'eq, mem_singleton] at this
    exact hl.1 this

variable [Fintype L]

/-- A node of the Lemke–Howson graph for the missing label `k₀`: a pair of label sets from the two
families having all labels except possibly `k₀`. -/
private def IsNode (VP VQ : Finset L → Prop) (k₀ : L) (p : Finset L × Finset L) : Prop :=
  VP p.1 ∧ VQ p.2 ∧ univ.erase k₀ ⊆ p.1 ∪ p.2

/-- A pivoting step in one of the two components. -/
private def Step (p q : Finset L × Finset L) : Prop :=
  (q.2 = p.2 ∧ ∃ c ∈ p.1, c ∉ q.1 ∧ p.1.erase c ⊆ q.1) ∨
    (q.1 = p.1 ∧ ∃ c ∈ p.2, c ∉ q.2 ∧ p.2.erase c ⊆ q.2)

/-- The Lemke–Howson graph. -/
private def lhGraph (VP VQ : Finset L → Prop) (k₀ : L) : SimpleGraph (Finset L × Finset L) :=
  SimpleGraph.fromRel fun p q => IsNode VP VQ k₀ p ∧ IsNode VP VQ k₀ q ∧ Step p q

variable {VP VQ : Finset L → Prop} {m n : ℕ} {k₀ : L}

private lemma step_symm (hPc : ∀ S, VP S → S.card = m) (hQc : ∀ T, VQ T → T.card = n)
    {p q : Finset L × Finset L} (hp : IsNode VP VQ k₀ p) (hq : IsNode VP VQ k₀ q)
    (h : Step q p) : Step p q := by
  rcases h with ⟨h2, c, hc, hc', hsub⟩ | ⟨h1, c, hc, hc', hsub⟩
  · obtain ⟨c', h1', h2', h3'⟩ := exists_back hPc hq.1 hp.1 hc hc' hsub
    exact Or.inl ⟨h2.symm, c', h1', h2', h3'⟩
  · obtain ⟨c', h1', h2', h3'⟩ := exists_back hQc hq.2.1 hp.2.1 hc hc' hsub
    exact Or.inr ⟨h1.symm, c', h1', h2', h3'⟩

private lemma lhGraph_adj (hPc : ∀ S, VP S → S.card = m) (hQc : ∀ T, VQ T → T.card = n)
    {p q : Finset L × Finset L} :
    (lhGraph VP VQ k₀).Adj p q ↔ IsNode VP VQ k₀ p ∧ IsNode VP VQ k₀ q ∧ Step p q := by
  rw [lhGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | ⟨hq, hp, h⟩⟩
    · exact h
    · exact ⟨hp, hq, step_symm hPc hQc hp hq h⟩
  · rintro ⟨hp, hq, h⟩
    refine ⟨?_, Or.inl ⟨hp, hq, h⟩⟩
    rintro rfl
    rcases h with ⟨-, c, hc, hc', -⟩ | ⟨-, c, hc, hc', -⟩ <;> exact hc' hc

private lemma degree_lhGraph [DecidableRel (lhGraph VP VQ k₀).Adj]
    (hPc : ∀ S, VP S → S.card = m) (hQc : ∀ T, VQ T → T.card = n)
    (hP : HasPivot VP) (hQ : HasPivot VQ) {S T : Finset L} (hST : IsNode VP VQ k₀ (S, T)) :
    (lhGraph VP VQ k₀).degree (S, T) =
      (S.filter (· ∈ insert k₀ T)).card + (T.filter (· ∈ insert k₀ S)).card := by
  have hS : VP S := hST.1
  have hT : VQ T := hST.2.1
  have hcov : univ.erase k₀ ⊆ S ∪ T := hST.2.2
  have hnb : (lhGraph VP VQ k₀).neighborFinset (S, T) =
      (S.filter (· ∈ insert k₀ T)).image (fun c => (piv VP S c, T)) ∪
        (T.filter (· ∈ insert k₀ S)).image (fun c => (S, piv VQ T c)) := by
    ext ⟨S', T'⟩
    rw [SimpleGraph.mem_neighborFinset, lhGraph_adj hPc hQc, mem_union, mem_image, mem_image]
    constructor
    · rintro ⟨-, hq, h | h⟩
      · obtain ⟨hT', c, hc, hc', hsub⟩ := h
        dsimp only at hT' hc hc' hsub
        subst hT'
        refine Or.inl ⟨c, mem_filter.2 ⟨hc, ?_⟩, ?_⟩
        · rw [mem_insert]
          by_cases hck : c = k₀
          · exact Or.inl hck
          · have := hq.2.2 (mem_erase.2 ⟨hck, mem_univ c⟩)
            rw [mem_union] at this
            exact Or.inr (this.resolve_left hc')
        · rw [← eq_piv hP hS hc (S' := S') ⟨hq.1, hc', hsub⟩]
      · obtain ⟨hS', c, hc, hc', hsub⟩ := h
        dsimp only at hS' hc hc' hsub
        subst hS'
        refine Or.inr ⟨c, mem_filter.2 ⟨hc, ?_⟩, ?_⟩
        · rw [mem_insert]
          by_cases hck : c = k₀
          · exact Or.inl hck
          · have := hq.2.2 (mem_erase.2 ⟨hck, mem_univ c⟩)
            rw [mem_union] at this
            exact Or.inr (this.resolve_right hc')
        · rw [← eq_piv hQ hT hc (S' := T') ⟨hq.2.1, hc', hsub⟩]
    · rintro (⟨c, hc, hq⟩ | ⟨c, hc, hq⟩)
      · rw [mem_filter, mem_insert] at hc
        obtain ⟨h1, h2, h3⟩ := piv_spec hP hS hc.1
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        refine ⟨hST, ⟨h1, hT, fun l hl => ?_⟩, Or.inl ⟨rfl, c, hc.1, h2, h3⟩⟩
        have hl' := hcov hl
        rw [mem_union] at hl' ⊢
        rcases hl' with hlS | hlT
        · by_cases hlc : l = c
          · subst hlc
            refine Or.inr (hc.2.resolve_left ?_)
            rintro rfl
            exact (mem_erase.1 hl).1 rfl
          · exact Or.inl (h3 (mem_erase.2 ⟨hlc, hlS⟩))
        · exact Or.inr hlT
      · rw [mem_filter, mem_insert] at hc
        obtain ⟨h1, h2, h3⟩ := piv_spec hQ hT hc.1
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        refine ⟨hST, ⟨hS, h1, fun l hl => ?_⟩, Or.inr ⟨rfl, c, hc.1, h2, h3⟩⟩
        have hl' := hcov hl
        rw [mem_union] at hl' ⊢
        rcases hl' with hlS | hlT
        · exact Or.inl hlS
        · by_cases hlc : l = c
          · subst hlc
            refine Or.inl (hc.2.resolve_left ?_)
            rintro rfl
            exact (mem_erase.1 hl).1 rfl
          · exact Or.inr (h3 (mem_erase.2 ⟨hlc, hlT⟩))
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hnb, card_union_of_disjoint]
  · rw [card_image_of_injOn, card_image_of_injOn]
    · intro c hc c' hc' h
      simp only [Prod.mk.injEq, true_and] at h
      by_contra hne
      have hc1 := (mem_filter.1 hc).1
      have hc'1 := (mem_filter.1 hc').1
      exact (piv_spec hQ hT hc'1).2.1 (h ▸ (piv_spec hQ hT hc1).2.2
        (mem_erase.2 ⟨Ne.symm hne, hc'1⟩))
    · intro c hc c' hc' h
      simp only [Prod.mk.injEq, and_true] at h
      by_contra hne
      have hc1 := (mem_filter.1 hc).1
      have hc'1 := (mem_filter.1 hc').1
      exact (piv_spec hP hS hc'1).2.1 (h ▸ (piv_spec hP hS hc1).2.2
        (mem_erase.2 ⟨Ne.symm hne, hc'1⟩))
  · rw [disjoint_left]
    rintro ⟨S', T'⟩ h1 h2
    rw [mem_image] at h1 h2
    obtain ⟨c, hc, hq⟩ := h1
    obtain ⟨c', -, hq'⟩ := h2
    simp only [Prod.mk.injEq] at hq hq'
    have hc1 := (mem_filter.1 hc).1
    have := (piv_spec hP hS hc1).2.1
    rw [hq.1, ← hq'.1] at this
    exact this hc1

private lemma odd_degree_lhGraph_iff [DecidableRel (lhGraph VP VQ k₀).Adj]
    (hcard : m + n = Fintype.card L)
    (hPc : ∀ S, VP S → S.card = m) (hQc : ∀ T, VQ T → T.card = n)
    (hP : HasPivot VP) (hQ : HasPivot VQ) (p : Finset L × Finset L) :
    Odd ((lhGraph VP VQ k₀).degree p) ↔ VP p.1 ∧ VQ p.2 ∧ p.1 ∪ p.2 = univ := by
  obtain ⟨S, T⟩ := p
  by_cases hnode : IsNode VP VQ k₀ (S, T)
  · rw [degree_lhGraph hPc hQc hP hQ hnode]
    have hS : VP S := hnode.1
    have hT : VQ T := hnode.2.1
    by_cases hU : S ∪ T = univ
    · simp only [hS, hT, hU, and_self, iff_true]
      have hinter : S ∩ T = ∅ := by
        have h := card_union_add_card_inter S T
        rw [hU, card_univ, hPc S hS, hQc T hT, ← hcard] at h
        exact card_eq_zero.1 (by omega)
      have hdisj : ∀ c ∈ S, c ∉ T := fun c hcS hcT => by
        simpa [hinter] using mem_inter.2 ⟨hcS, hcT⟩
      have h1 : S.filter (· ∈ insert k₀ T) = S.filter (· = k₀) :=
        filter_congr fun c hc => by
          rw [mem_insert]
          exact or_iff_left (hdisj c hc)
      have h2 : T.filter (· ∈ insert k₀ S) = T.filter (· = k₀) :=
        filter_congr fun c hc => by
          rw [mem_insert]
          exact or_iff_left fun h => hdisj c h hc
      rw [h1, h2, filter_eq', filter_eq']
      have hk : k₀ ∈ S ∪ T := hU ▸ mem_univ k₀
      rw [mem_union] at hk
      rcases hk with hk | hk
      · simp [hk, hdisj k₀ hk]
      · have hkS : k₀ ∉ S := fun h => hdisj k₀ h hk
        simp [hk, hkS]
    · simp only [hU, and_false, iff_false, Nat.not_odd_iff_even]
      have hk : k₀ ∉ S ∪ T := fun hk => hU <| eq_univ_of_forall fun l => by
        by_cases hl : l = k₀
        · exact hl ▸ hk
        · exact hnode.2.2 (mem_erase.2 ⟨hl, mem_univ l⟩)
      rw [mem_union, not_or] at hk
      have h1 : S.filter (· ∈ insert k₀ T) = S ∩ T := by
        rw [← filter_mem_eq_inter]
        exact filter_congr fun c hc => by
          rw [mem_insert, or_iff_right]
          rintro rfl
          exact hk.1 hc
      have h2 : T.filter (· ∈ insert k₀ S) = S ∩ T := by
        rw [inter_comm, ← filter_mem_eq_inter]
        exact filter_congr fun c hc => by
          rw [mem_insert, or_iff_right]
          rintro rfl
          exact hk.2 hc
      rw [h1, h2]
      exact ⟨_, rfl⟩
  · have hdeg : (lhGraph VP VQ k₀).degree (S, T) = 0 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, card_eq_zero]
      ext q
      simp only [SimpleGraph.mem_neighborFinset, lhGraph_adj hPc hQc, notMem_empty, iff_false]
      exact fun h => hnode h.1
    rw [hdeg]
    simp only [Nat.not_odd_zero, false_iff]
    rintro ⟨hS, hT, hU⟩
    exact hnode ⟨hS, hT, hU ▸ erase_subset k₀ univ⟩

/-- **Parity of completely labelled pairs.** If two families of label sets of sizes `m` and `n`,
with `m + n` labels in total, both have the pivoting property, then the number of pairs covering
all labels is even. -/
private lemma even_ncard_completelyLabeled (k₀ : L) (hcard : m + n = Fintype.card L)
    (hPc : ∀ S, VP S → S.card = m) (hQc : ∀ T, VQ T → T.card = n)
    (hP : HasPivot VP) (hQ : HasPivot VQ) :
    Even {p : Finset L × Finset L | VP p.1 ∧ VQ p.2 ∧ p.1 ∪ p.2 = univ}.ncard := by
  classical
  have h := (lhGraph VP VQ k₀).even_card_odd_degree_vertices
  convert h using 2
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext p
  simp only [Set.mem_toFinset, Set.mem_ofPred_eq, mem_filter, mem_univ, true_and]
  exact (odd_degree_lhGraph_iff hcard hPc hQc hP hQ p).symm

end Parity

section Polytope

variable {ι κ : Type*} [Fintype ι]

/-- Slacks of the inequalities `0 ≤ x i` and `∑ i, x i * C i k ≤ 1` defining the polytope
`{x | 0 ≤ x, xᵀ C ≤ 1}`. -/
private def slack (C : ι → κ → ℝ) (x : ι → ℝ) : ι ⊕ κ → ℝ :=
  Sum.elim x fun k => 1 - ∑ i, x i * C i k

/-- The linear part of `slack`. -/
private def slackLin (C : ι → κ → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι ⊕ κ → ℝ) where
  toFun w := Sum.elim w fun k => -∑ i, w i * C i k
  map_add' u w := by
    funext l
    cases l <;> simp [add_mul, sum_add_distrib, add_comm]
  map_smul' t w := by
    funext l
    cases l <;> simp [mul_assoc, mul_sum]

private lemma slackLin_apply (C : ι → κ → ℝ) (w : ι → ℝ) :
    slackLin C w = Sum.elim w fun k => -∑ i, w i * C i k := rfl

private lemma slack_add_smul (C : ι → κ → ℝ) (x w : ι → ℝ) (t : ℝ) (l : ι ⊕ κ) :
    slack C (x + t • w) l = slack C x l + t * slackLin C w l := by
  cases l with
  | inl i => simp [slack, slackLin_apply]
  | inr k =>
    simp only [slack, slackLin_apply, Sum.elim_inr, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
    ring

private lemma slack_sub_slack (C : ι → κ → ℝ) (x x' : ι → ℝ) (l : ι ⊕ κ) :
    slack C x' l - slack C x l = slackLin C (x' - x) l := by
  cases l <;> simp [slack, slackLin_apply, sub_mul, sum_sub_distrib]

variable [Fintype κ]

/-- `x` lies in the polytope `{x | 0 ≤ x, xᵀ C ≤ 1}`. -/
private def InPoly (C : ι → κ → ℝ) (x : ι → ℝ) : Prop := ∀ l, 0 ≤ slack C x l

/-- The labels of `x`: the indices of its tight inequalities. -/
private noncomputable def lab (C : ι → κ → ℝ) (x : ι → ℝ) : Finset (ι ⊕ κ) :=
  (univ.filter fun i => x i = 0).disjSum (univ.filter fun k => ∑ i, x i * C i k = 1)

private lemma mem_lab {C : ι → κ → ℝ} {x : ι → ℝ} {l : ι ⊕ κ} :
    l ∈ lab C x ↔ slack C x l = 0 := by
  cases l with
  | inl i => simp [lab, slack, eq_comm]
  | inr k =>
    simp only [lab, slack, inr_mem_disjSum, mem_filter, mem_univ, true_and, Sum.elim_inr]
    rw [sub_eq_zero, eq_comm]

variable {C : ι → κ → ℝ}

omit [Fintype κ] in
/-- **Ratio test.** Moving from a point of the polytope along a direction that decreases some
slack, there is a largest step keeping all slacks nonnegative; it makes some decreasing slack
zero. -/
private lemma exists_ratio [Finite κ] {x w : ι → ℝ} (hx : InPoly C x)
    (hw : ∃ l, slackLin C w l < 0) :
    ∃ t : ℝ, 0 ≤ t ∧ (∃ l₀, slackLin C w l₀ < 0 ∧ slack C x l₀ + t * slackLin C w l₀ = 0) ∧
      InPoly C (x + t • w) ∧ ∀ l, slackLin C w l < 0 → 0 ≤ slack C x l + t * slackLin C w l := by
  classical
  have := Fintype.ofFinite κ
  set R := univ.filter fun l => slackLin C w l < 0
  have hR : R.Nonempty := by
    obtain ⟨l, hl⟩ := hw
    exact ⟨l, mem_filter.2 ⟨mem_univ l, hl⟩⟩
  obtain ⟨l₀, hl₀R, hmin⟩ := R.exists_min_image (fun l => slack C x l / -slackLin C w l) hR
  have hl₀ : slackLin C w l₀ < 0 := (mem_filter.1 hl₀R).2
  set t := slack C x l₀ / -slackLin C w l₀ with ht_def
  have ht : 0 ≤ t := div_nonneg (hx l₀) (by linarith)
  have hfeas : ∀ l, slackLin C w l < 0 → 0 ≤ slack C x l + t * slackLin C w l := by
    intro l hl
    have := hmin l (mem_filter.2 ⟨mem_univ l, hl⟩)
    rw [le_div_iff₀ (by linarith)] at this
    linarith
  refine ⟨t, ht, ⟨l₀, hl₀, ?_⟩, fun l => ?_, hfeas⟩
  · rw [ht_def, div_mul_eq_mul_div, mul_div_assoc, div_neg, div_self hl₀.ne, mul_neg, mul_one,
      add_neg_cancel]
  · rw [slack_add_smul]
    rcases lt_or_ge (slackLin C w l) 0 with hl | hl
    · exact hfeas l hl
    · exact add_nonneg (hx l) (mul_nonneg ht hl)

/-- At a point of the polytope with at least `card ι` labels, no nonzero direction keeps all its
labels: otherwise the ratio test would give a point with one label more. -/
private lemma eq_zero_of_forall_lab (hrec : ∀ w : ι → ℝ, w ≠ 0 → ∃ l, slackLin C w l < 0)
    (hnd : ∀ x, InPoly C x → (lab C x).card ≤ Fintype.card ι) {x w : ι → ℝ} (hx : InPoly C x)
    (hcard : Fintype.card ι ≤ (lab C x).card) (hw : ∀ l ∈ lab C x, slackLin C w l = 0) :
    w = 0 := by
  classical
  by_contra hw0
  obtain ⟨t, -, ⟨l₀, hl₀, htight⟩, hin, -⟩ := exists_ratio hx (hrec w hw0)
  have hl₀lab : l₀ ∉ lab C x := fun h => by linarith [hw l₀ h]
  have hsub : insert l₀ (lab C x) ⊆ lab C (x + t • w) := by
    intro l hl
    rw [mem_insert] at hl
    rw [mem_lab, slack_add_smul]
    rcases hl with rfl | hl
    · exact htight
    · rw [mem_lab.1 hl, hw l hl]
      ring
  have h1 := card_le_card hsub
  rw [card_insert_of_notMem hl₀lab] at h1
  have h2 := hnd _ hin
  omega

/-- A vertex (a point with `card ι` labels) is determined by its labels. -/
private lemma eq_of_lab_eq (hrec : ∀ w : ι → ℝ, w ≠ 0 → ∃ l, slackLin C w l < 0)
    (hnd : ∀ x, InPoly C x → (lab C x).card ≤ Fintype.card ι) {x x' : ι → ℝ}
    (hx : InPoly C x) (hcard : Fintype.card ι ≤ (lab C x).card) (h : lab C x = lab C x') :
    x = x' := by
  have := eq_zero_of_forall_lab hrec hnd hx hcard (w := x' - x) fun l hl => by
    rw [← slack_sub_slack, mem_lab.1 hl, mem_lab.1 (h ▸ hl), sub_zero]
  exact (sub_eq_zero.1 this).symm

/-- **Pivoting.** Dropping a label `c` of a vertex `x` leads along an edge of the polytope to
exactly one other vertex keeping the other labels of `x`. -/
private lemma exists_pivot [DecidableEq ι] [DecidableEq κ]
    (hrec : ∀ w : ι → ℝ, w ≠ 0 → ∃ l, slackLin C w l < 0)
    (hnd : ∀ x, InPoly C x → (lab C x).card ≤ Fintype.card ι) {x : ι → ℝ} (hx : InPoly C x)
    (hcard : (lab C x).card = Fintype.card ι) {c : ι ⊕ κ} (hc : c ∈ lab C x) :
    ∃ x', InPoly C x' ∧ (lab C x').card = Fintype.card ι ∧ c ∉ lab C x' ∧
      (lab C x).erase c ⊆ lab C x' ∧
      ∀ x'', InPoly C x'' → (lab C x'').card = Fintype.card ι → c ∉ lab C x'' →
        (lab C x).erase c ⊆ lab C x'' → x'' = x' := by
  set T := (lab C x).erase c with hT_def
  have hTcard : T.card + 1 = Fintype.card ι := by
    have := card_pos.2 ⟨c, hc⟩
    rw [card_erase_of_mem hc]
    omega
  -- a nonzero direction keeping the labels in `T`
  let Φ : (ι → ℝ) →ₗ[ℝ] (T → ℝ) :=
    LinearMap.funLeft ℝ ℝ (Subtype.val : T → ι ⊕ κ) ∘ₗ slackLin C
  have hker : LinearMap.ker Φ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe]
    omega)
  obtain ⟨w₀, hw₀ker, hw₀⟩ := (Submodule.ne_bot_iff _).1 hker
  have hw₀T : ∀ l ∈ T, slackLin C w₀ l = 0 := fun l hl =>
    congrFun (LinearMap.mem_ker.1 hw₀ker) ⟨l, hl⟩
  have hw₀c : slackLin C w₀ c ≠ 0 := by
    intro h0
    refine hw₀ (eq_zero_of_forall_lab hrec hnd hx hcard.ge fun l hl => ?_)
    by_cases hlc : l = c
    · rw [hlc]
      exact h0
    · exact hw₀T l (mem_erase.2 ⟨hlc, hl⟩)
  -- normalise it so that the slack of `c` increases at unit rate
  set w := (slackLin C w₀ c)⁻¹ • w₀ with hw_def
  have hwl : ∀ l, slackLin C w l = (slackLin C w₀ c)⁻¹ * slackLin C w₀ l := fun l => by
    rw [hw_def, map_smul, Pi.smul_apply, smul_eq_mul]
  have hwc : slackLin C w c = 1 := by
    rw [hwl]
    exact inv_mul_cancel₀ hw₀c
  have hwT : ∀ l ∈ T, slackLin C w l = 0 := fun l hl => by rw [hwl, hw₀T l hl, mul_zero]
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, map_zero, Pi.zero_apply] at hwc
    exact zero_ne_one hwc
  obtain ⟨t, -, ⟨l₀, hl₀, htight⟩, hin, hfeas⟩ := exists_ratio hx (hrec w hw0)
  have hl₀lab : l₀ ∉ lab C x := by
    intro h
    by_cases hlc : l₀ = c
    · rw [hlc, hwc] at hl₀
      linarith
    · rw [hwT l₀ (mem_erase.2 ⟨hlc, h⟩)] at hl₀
      exact lt_irrefl 0 hl₀
  have hslack_pos : ∀ l, l ∉ lab C x → 0 < slack C x l := fun l hl =>
    lt_of_le_of_ne (hx l) fun h => hl (mem_lab.2 h.symm)
  have htpos : 0 < t := by
    have := hslack_pos l₀ hl₀lab
    nlinarith
  have hsubT : T ⊆ lab C (x + t • w) := fun l hl => by
    rw [mem_lab, slack_add_smul, mem_lab.1 (mem_of_mem_erase hl), hwT l hl]
    ring
  have hl₀' : l₀ ∈ lab C (x + t • w) := by
    rw [mem_lab, slack_add_smul]
    exact htight
  have hl₀T : l₀ ∉ T := fun h => hl₀lab (mem_of_mem_erase h)
  have hcard' : (lab C (x + t • w)).card = Fintype.card ι := by
    refine le_antisymm (hnd _ hin) ?_
    have := card_le_card (insert_subset hl₀' hsubT)
    rw [card_insert_of_notMem hl₀T] at this
    omega
  refine ⟨x + t • w, hin, hcard', ?_, hsubT, ?_⟩
  · rw [mem_lab, slack_add_smul, mem_lab.1 hc, hwc]
    linarith
  · intro x'' hx'' hcard'' hc'' hsub''
    set s := slackLin C (x'' - x) c with hs_def
    have hu : x'' - x = s • w := by
      have := eq_zero_of_forall_lab hrec hnd hx hcard.ge (w := x'' - x - s • w) fun l hl => by
        rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        by_cases hlc : l = c
        · rw [hlc, hwc, ← hs_def]
          ring
        · have hlT : l ∈ T := mem_erase.2 ⟨hlc, hl⟩
          rw [hwT l hlT, ← slack_sub_slack, mem_lab.1 (hsub'' hlT), mem_lab.1 hl]
          ring
      exact sub_eq_zero.1 this
    have hx''eq : x'' = x + s • w := by
      rw [← hu]
      abel
    have hsl : ∀ l, slack C x'' l = slack C x l + s * slackLin C w l := fun l => by
      rw [hx''eq, slack_add_smul]
    have hspos : 0 < s := by
      have h1 := hsl c
      rw [mem_lab.1 hc, hwc, zero_add, mul_one] at h1
      have h2 : slack C x'' c ≠ 0 := fun h => hc'' (mem_lab.2 h)
      rw [h1] at h2
      exact lt_of_le_of_ne (h1 ▸ hx'' c) (Ne.symm h2)
    have hst : s ≤ t := by
      have h1 := hx'' l₀
      rw [hsl] at h1
      nlinarith
    have hts : t ≤ s := by
      by_contra hlt
      rw [not_le] at hlt
      have hsub : lab C x'' ⊆ T := by
        intro l hl
        have hl0 : slack C x'' l = 0 := mem_lab.1 hl
        by_cases hlx : l ∈ lab C x
        · exact mem_erase.2 ⟨fun h => hc'' (h ▸ hl), hlx⟩
        · exfalso
          have hpos := hslack_pos l hlx
          rw [hsl] at hl0
          rcases lt_or_ge (slackLin C w l) 0 with hneg | hnn
          · have := hfeas l hneg
            nlinarith
          · nlinarith
      have := card_le_card hsub
      omega
    rw [hx''eq, le_antisymm hst hts]

/-- The label sets of the vertices of the polytope. -/
private def VS (C : ι → κ → ℝ) (S : Finset (ι ⊕ κ)) : Prop :=
  ∃ x, InPoly C x ∧ lab C x = S ∧ S.card = Fintype.card ι

private lemma hasPivot_VS [DecidableEq ι] [DecidableEq κ]
    (hrec : ∀ w : ι → ℝ, w ≠ 0 → ∃ l, slackLin C w l < 0)
    (hnd : ∀ x, InPoly C x → (lab C x).card ≤ Fintype.card ι) : HasPivot (VS C) := by
  rintro S ⟨x, hx, rfl, hcard⟩ c hc
  obtain ⟨x', hx', hcard', hc', hsub', huniq⟩ := exists_pivot hrec hnd hx hcard hc
  refine ⟨lab C x', ⟨⟨x', hx', rfl, hcard'⟩, hc', hsub'⟩, ?_⟩
  rintro S'' ⟨⟨x'', hx'', rfl, hcard''⟩, hc'', hsub''⟩
  rw [huniq x'' hx'' hcard'' hc'' hsub'']

omit [Fintype κ] in
private lemma inPoly_zero : InPoly C 0 := by
  rintro (i | k) <;> simp [slack]

private lemma inr_notMem_lab_zero (k : κ) : Sum.inr k ∉ lab C 0 := by
  simp [lab]

private lemma card_lab_zero : (lab C 0).card = Fintype.card ι := by
  simp [lab]

end Polytope

section Simplex

variable {ι κ : Type*} [Fintype ι] {C : ι → κ → ℝ}

/-- With positive entries, the polytope `{x | 0 ≤ x, xᵀ C ≤ 1}` is bounded: every nonzero
direction decreases some slack. -/
private lemma recession [Nonempty κ] (hC : ∀ i k, 0 < C i k) (w : ι → ℝ) (hw : w ≠ 0) :
    ∃ l, slackLin C w l < 0 := by
  by_cases h : ∃ i, w i < 0
  · obtain ⟨i, hi⟩ := h
    exact ⟨Sum.inl i, by simpa [slackLin_apply] using hi⟩
  · simp only [not_exists, not_lt] at h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
    obtain ⟨k⟩ := ‹Nonempty κ›
    refine ⟨Sum.inr k, ?_⟩
    have : 0 < ∑ i, w i * C i k := sum_pos' (fun j _ => mul_nonneg (h j) (hC j k).le)
      ⟨i, mem_univ i, mul_pos (lt_of_le_of_ne (h i) (Ne.symm hi)) (hC i k)⟩
    simpa [slackLin_apply] using this

private lemma sum_mul_le_one {x : ι → ℝ} (hx : InPoly C x) (k : κ) : ∑ i, x i * C i k ≤ 1 := by
  have := hx (Sum.inr k)
  simp only [slack, Sum.elim_inr, sub_nonneg] at this
  exact this

/-- The point of the simplex on the ray through a nonzero point `x` of the polytope. -/
private noncomputable def toSimplex {x : ι → ℝ} (hx : InPoly C x) (hs : 0 < ∑ i, x i) :
    StdSimplex ℝ ι :=
  StdSimplex.ofWeights (fun i => x i / ∑ j, x j) (fun i => div_nonneg (hx (Sum.inl i)) hs.le)
    (by rw [← sum_div, div_self hs.ne'])

private lemma toSimplex_weights {x : ι → ℝ} (hx : InPoly C x) (hs : 0 < ∑ i, x i) (i : ι) :
    (toSimplex hx hs).weights i = x i / ∑ j, x j :=
  StdSimplex.ofWeights_weights _ _ _ i

variable [Fintype κ]

private lemma sum_pos_of_inr_mem_lab {x : ι → ℝ} (hx : InPoly C x) {k : κ}
    (hk : Sum.inr k ∈ lab C x) : 0 < ∑ i, x i := by
  have hx0 : ∀ i, 0 ≤ x i := fun i => hx (Sum.inl i)
  rcases (sum_nonneg fun i (_ : i ∈ univ) => hx0 i).eq_or_lt with h | h
  · have h0 : ∀ i, x i = 0 := fun i =>
      (sum_eq_zero_iff_of_nonneg fun i _ => hx0 i).1 h.symm i (mem_univ i)
    simp [lab, h0] at hk
  · exact h

/-- One player's half of nondegeneracy bounds the number of labels of a point of the
polytope by the dimension. -/
private lemma card_lab_le
    (hnd : ∀ x : StdSimplex ℝ ι, (bestResponses₂ C x).card ≤ x.weights.support.card)
    {x : ι → ℝ} (hx : InPoly C x) : (lab C x).card ≤ Fintype.card ι := by
  classical
  rw [lab, card_disjSum]
  set K := univ.filter fun k => ∑ i, x i * C i k = 1 with hK_def
  rcases K.eq_empty_or_nonempty with hK | ⟨k₁, hk₁⟩
  · rw [hK, card_empty, add_zero]
    exact card_le_univ _
  · have hs := sum_pos_of_inr_mem_lab hx (k := k₁) (by rw [lab, inr_mem_disjSum]; exact hk₁)
    set xh := toSimplex hx hs
    have hsupp : xh.weights.support = univ.filter fun i => ¬ x i = 0 := by
      ext i
      simp [xh, Finsupp.mem_support_iff, toSimplex_weights, hs.ne']
    have hKsub : K ⊆ bestResponses₂ C xh := by
      intro k hk
      have hk' := (mem_filter.1 hk).2
      simp only [bestResponses₂, mem_filter, mem_univ, true_and]
      intro k'
      simp only [xh, toSimplex_weights, div_mul_eq_mul_div, ← sum_div]
      exact div_le_div_of_nonneg_right (hk' ▸ sum_mul_le_one hx k') hs.le
    have h1 := (card_le_card hKsub).trans (hnd xh)
    rw [hsupp] at h1
    have h2 := card_filter_add_card_filter_not (s := univ) fun i => x i = 0
    rw [card_univ] at h2
    omega

variable [Nonempty κ]

/-- The opponent's best expected payoff against the mixed strategy `x`. -/
private noncomputable def maxPay (C : ι → κ → ℝ) (x : StdSimplex ℝ ι) : ℝ :=
  univ.sup' univ_nonempty fun k => ∑ i, x.weights i * C i k

private lemma le_maxPay (x : StdSimplex ℝ ι) (k : κ) : ∑ i, x.weights i * C i k ≤ maxPay C x :=
  le_sup' (fun k => ∑ i, x.weights i * C i k) (mem_univ k)

private lemma maxPay_pos (hC : ∀ i k, 0 < C i k) (x : StdSimplex ℝ ι) : 0 < maxPay C x := by
  obtain ⟨k⟩ := ‹Nonempty κ›
  refine lt_of_lt_of_le ?_ (le_maxPay x k)
  obtain ⟨i, hi⟩ : ∃ i, x.weights i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have := x.total_of_fintype
    simp [h] at this
  exact sum_pos' (fun j _ => mul_nonneg (x.weights_nonneg j) (hC j k).le)
    ⟨i, mem_univ i, mul_pos (lt_of_le_of_ne (x.weights_nonneg i) (Ne.symm hi)) (hC i k)⟩

/-- The point of the polytope on the ray through the mixed strategy `x`, on the face where
the opponent's best payoff is `1`. -/
private noncomputable def toPoly (C : ι → κ → ℝ) (x : StdSimplex ℝ ι) : ι → ℝ :=
  fun i => x.weights i / maxPay C x

private lemma sum_toPoly_mul (C : ι → κ → ℝ) (x : StdSimplex ℝ ι) (k : κ) :
    ∑ i, toPoly C x i * C i k = (∑ i, x.weights i * C i k) / maxPay C x := by
  simp only [toPoly, div_mul_eq_mul_div, sum_div]

private lemma inPoly_toPoly (hC : ∀ i k, 0 < C i k) (x : StdSimplex ℝ ι) :
    InPoly C (toPoly C x) := by
  rintro (i | k)
  · exact div_nonneg (x.weights_nonneg i) (maxPay_pos hC x).le
  · simp only [slack, Sum.elim_inr, sum_toPoly_mul, sub_nonneg]
    rw [div_le_one (maxPay_pos hC x)]
    exact le_maxPay x k

private lemma inl_mem_lab_toPoly (hC : ∀ i k, 0 < C i k) (x : StdSimplex ℝ ι) (i : ι) :
    Sum.inl i ∈ lab C (toPoly C x) ↔ x.weights i = 0 := by
  simp [lab, toPoly, (maxPay_pos hC x).ne']

private lemma inr_mem_lab_toPoly (hC : ∀ i k, 0 < C i k) (x : StdSimplex ℝ ι) (k : κ) :
    Sum.inr k ∈ lab C (toPoly C x) ↔ k ∈ bestResponses₂ C x := by
  rw [lab, inr_mem_disjSum, mem_filter, sum_toPoly_mul, div_eq_one_iff_eq (maxPay_pos hC x).ne']
  simp only [mem_univ, true_and, bestResponses₂, mem_filter]
  constructor
  · intro h k'
    rw [h]
    exact le_maxPay x k'
  · intro h
    exact le_antisymm (le_maxPay x k) (sup'_le _ _ fun k' _ => h k')

private lemma toPoly_injective (hC : ∀ i k, 0 < C i k) {x x' : StdSimplex ℝ ι}
    (h : toPoly C x = toPoly C x') : x = x' := by
  have hs : ∀ y : StdSimplex ℝ ι, ∑ i, toPoly C y i = (maxPay C y)⁻¹ := fun y => by
    simp only [toPoly, ← sum_div, y.total_of_fintype, one_div]
  have hm : maxPay C x = maxPay C x' := by
    have := hs x
    rw [h, hs x'] at this
    exact inv_injective this.symm
  refine StdSimplex.ext (Finsupp.ext fun i => ?_)
  have := congrFun h i
  simp only [toPoly, hm] at this
  exact (div_left_inj₀ (maxPay_pos hC x').ne').1 this

/-- A point of the polytope on the face where some opponent's constraint is tight is the image
of a mixed strategy. -/
private lemma exists_toPoly_eq {x : ι → ℝ} (hx : InPoly C x) {k₁ : κ}
    (hk₁ : Sum.inr k₁ ∈ lab C x) : ∃ xh : StdSimplex ℝ ι, toPoly C xh = x := by
  have hs := sum_pos_of_inr_mem_lab hx hk₁
  have hk : ∑ i, x i * C i k₁ = 1 := by simpa [lab] using hk₁
  set xh := toSimplex hx hs
  have hval : ∀ k, ∑ i, xh.weights i * C i k = (∑ i, x i * C i k) / ∑ j, x j := fun k => by
    simp only [xh, toSimplex_weights, div_mul_eq_mul_div, sum_div]
  have hmax : maxPay C xh = (∑ j, x j)⁻¹ := by
    apply le_antisymm
    · refine sup'_le _ _ fun k _ => ?_
      rw [hval, ← one_div]
      exact div_le_div_of_nonneg_right (sum_mul_le_one hx k) hs.le
    · calc (∑ j, x j)⁻¹ = ∑ i, xh.weights i * C i k₁ := by rw [hval, hk, one_div]
        _ ≤ maxPay C xh := le_maxPay xh k₁
  refine ⟨xh, funext fun i => ?_⟩
  simp only [toPoly, hmax, xh, toSimplex_weights]
  field_simp

end Simplex

section Nash

/-- **Best response condition** for one player: against the payoff vector `p`, a mixed
strategy `z` is optimal iff every pure strategy it uses is a pure best response. -/
private lemma optimal_iff {ι : Type*} [Fintype ι] (p : ι → ℝ) (z : StdSimplex ℝ ι) :
    (∀ z' : StdSimplex ℝ ι, ∑ i, z'.weights i * p i ≤ ∑ i, z.weights i * p i) ↔
      ∀ i, z.weights i ≠ 0 → ∀ i', p i' ≤ p i := by
  classical
  have hsum : ∀ (z' : StdSimplex ℝ ι) (c : ℝ), ∑ i, z'.weights i * c = c := fun z' c => by
    rw [← sum_mul, z'.total_of_fintype, one_mul]
  constructor
  · intro h i hi i'
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨imax, -, himax⟩ := univ.exists_max_image p ⟨i, mem_univ i⟩
    have h1 := h (StdSimplex.single imax)
    simp only [StdSimplex.weights_single, Finsupp.single_apply, ite_mul, one_mul, zero_mul,
      sum_ite_eq, mem_univ, ite_true] at h1
    have h2 : ∑ k, z.weights k * p k < ∑ k, z.weights k * p imax := by
      apply sum_lt_sum
      · exact fun k _ => mul_le_mul_of_nonneg_left (himax k (mem_univ k)) (z.weights_nonneg k)
      · exact ⟨i, mem_univ i, mul_lt_mul_of_pos_left (hlt.trans_le (himax i' (mem_univ i')))
          (lt_of_le_of_ne (z.weights_nonneg i) (Ne.symm hi))⟩
    rw [hsum] at h2
    linarith
  · intro h z'
    obtain ⟨i₀, hi₀⟩ := z.support_weights_nonempty
    rw [Finsupp.mem_support_iff] at hi₀
    have hmax : ∀ k, p k ≤ p i₀ := h i₀ hi₀
    have heq : ∑ i, z.weights i * p i = p i₀ := by
      rw [← hsum z (p i₀)]
      refine sum_congr rfl fun i _ => ?_
      by_cases hi : z.weights i = 0
      · rw [hi, zero_mul, zero_mul]
      · rw [le_antisymm (hmax i) (h i hi i₀)]
    rw [heq, ← hsum z' (p i₀)]
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hmax i) (z'.weights_nonneg i)

private lemma bilinPayoff_eq_left (C : M → N → ℝ) (x : StdSimplex ℝ M) (y : StdSimplex ℝ N) :
    bilinPayoff C x y = ∑ i, x.weights i * ∑ j, C i j * y.weights j := by
  simp only [bilinPayoff, mul_sum, mul_assoc]

private lemma bilinPayoff_eq_right (C : M → N → ℝ) (x : StdSimplex ℝ M) (y : StdSimplex ℝ N) :
    bilinPayoff C x y = ∑ j, y.weights j * ∑ i, x.weights i * C i j := by
  rw [bilinPayoff, sum_comm]
  simp only [mul_sum]
  exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by ring

/-- **Best response condition.** In a finite bimatrix game `(A, B)` with real payoff
matrices, `(x, y)` is a Nash equilibrium iff every pure strategy used by either player is a
pure best response to the other's. -/
theorem isBimatrixNash_iff (A B : M → N → ℝ) (x : StdSimplex ℝ M) (y : StdSimplex ℝ N) :
    IsBimatrixNash A B x y ↔ (∀ i, x.weights i ≠ 0 → i ∈ bestResponses₁ A y) ∧
      ∀ j, y.weights j ≠ 0 → j ∈ bestResponses₂ B x := by
  rw [IsBimatrixNash]
  simp only [bilinPayoff_eq_left A, bilinPayoff_eq_right B]
  refine (Iff.and (optimal_iff _ x) (optimal_iff _ y)).trans ?_
  simp [bestResponses₁, bestResponses₂]

private lemma bestResponses₂_swap (A : M → N → ℝ) (y : StdSimplex ℝ N) :
    bestResponses₂ (Function.swap A) y = bestResponses₁ A y := by
  ext i
  simp [bestResponses₁, bestResponses₂, Function.swap, mul_comm]

/-- The pivoting property is transported along a bijection of labels. -/
private lemma hasPivot_map {L L' : Type*} [DecidableEq L] [DecidableEq L'] (e : L ≃ L')
    {V : Finset L' → Prop} (hV : HasPivot V) :
    HasPivot fun T : Finset L => V (T.map e.toEmbedding) := by
  intro T hT c hc
  obtain ⟨S', ⟨hS'V, hcS', hsub⟩, huniq⟩ := hV _ hT (e c) (mem_map_of_mem _ hc)
  have hback : (S'.map e.symm.toEmbedding).map e.toEmbedding = S' := by
    ext l
    simp
  have hme : (T.map e.toEmbedding).erase (e c) = (T.erase c).map e.toEmbedding :=
    (map_erase e.toEmbedding T c).symm
  refine ⟨S'.map e.symm.toEmbedding, ⟨?_, ?_, fun l hl => ?_⟩, ?_⟩
  · change V ((S'.map e.symm.toEmbedding).map e.toEmbedding)
    rw [hback]
    exact hS'V
  · rwa [mem_map_equiv, Equiv.symm_symm]
  · rw [mem_map_equiv, Equiv.symm_symm]
    refine hsub ?_
    rw [hme]
    exact mem_map_of_mem _ hl
  · rintro T' ⟨hT'V, hcT', hsubT'⟩
    have hT'map : T'.map e.toEmbedding = S' := by
      refine huniq _ ⟨hT'V, ?_, ?_⟩
      · rwa [mem_map_equiv, Equiv.symm_apply_apply]
      · rw [hme]
        exact map_subset_map.2 hsubT'
    rw [← hT'map]
    ext l
    simp

omit [Fintype M] [Fintype N] in
private lemma inl_mem_map_sumComm {s : Finset (N ⊕ M)} {i : M} :
    Sum.inl i ∈ s.map (Equiv.sumComm N M).toEmbedding ↔ Sum.inr i ∈ s := by
  rw [mem_map_equiv, Equiv.sumComm_symm, Equiv.sumComm_apply, Sum.swap_inl]

omit [Fintype M] [Fintype N] in
private lemma inr_mem_map_sumComm {s : Finset (N ⊕ M)} {j : N} :
    Sum.inr j ∈ s.map (Equiv.sumComm N M).toEmbedding ↔ Sum.inl j ∈ s := by
  rw [mem_map_equiv, Equiv.sumComm_symm, Equiv.sumComm_apply, Sum.swap_inr]

variable [Nonempty M] [Nonempty N]

/-- The labels of player 1's mixed strategy `x`: the pure strategies it does not use and
player 2's pure best responses to it. They are the labels of the corresponding point of player
1's best response polytope. -/
private noncomputable def labS (B : M → N → ℝ) (x : StdSimplex ℝ M) : Finset (M ⊕ N) :=
  lab B (toPoly B x)

/-- The labels of player 2's mixed strategy `y`: player 1's pure best responses to it and the
pure strategies it does not use. -/
private noncomputable def labT (A : M → N → ℝ) (y : StdSimplex ℝ N) : Finset (M ⊕ N) :=
  (lab (Function.swap A) (toPoly (Function.swap A) y)).map (Equiv.sumComm N M).toEmbedding

/-- **Equilibria are the completely labelled pairs.** -/
private lemma isBimatrixNash_iff_union [DecidableEq M] [DecidableEq N] {A B : M → N → ℝ}
    (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) (x : StdSimplex ℝ M) (y : StdSimplex ℝ N) :
    IsBimatrixNash A B x y ↔ labS B x ∪ labT A y = univ := by
  rw [isBimatrixNash_iff, eq_univ_iff_forall]
  have hA' : ∀ j i, 0 < Function.swap A j i := fun j i => hA i j
  constructor
  · rintro ⟨h1, h2⟩ (i | j)
    · rw [mem_union, labS, labT, inl_mem_map_sumComm, inl_mem_lab_toPoly hB,
        inr_mem_lab_toPoly hA', bestResponses₂_swap]
      by_cases hx : x.weights i = 0
      · exact Or.inl hx
      · exact Or.inr (h1 i hx)
    · rw [mem_union, labS, labT, inr_mem_map_sumComm, inr_mem_lab_toPoly hB,
        inl_mem_lab_toPoly hA']
      by_cases hy : y.weights j = 0
      · exact Or.inr hy
      · exact Or.inl (h2 j hy)
  · intro hU
    refine ⟨fun i hi => ?_, fun j hj => ?_⟩
    · have := hU (Sum.inl i)
      rw [mem_union, labS, labT, inl_mem_map_sumComm, inl_mem_lab_toPoly hB,
        inr_mem_lab_toPoly hA', bestResponses₂_swap] at this
      exact this.resolve_left hi
    · have := hU (Sum.inr j)
      rw [mem_union, labS, labT, inr_mem_map_sumComm, inr_mem_lab_toPoly hB,
        inl_mem_lab_toPoly hA'] at this
      exact this.resolve_right hj

/-- The theorem for positive payoff matrices, by the Lemke–Howson parity argument. -/
private theorem odd_ncard_of_pos (A B : M → N → ℝ) (hA : ∀ i j, 0 < A i j)
    (hB : ∀ i j, 0 < B i j) (h : IsNondegenerate A B) :
    Odd {p : StdSimplex ℝ M × StdSimplex ℝ N | IsBimatrixNash A B p.1 p.2}.ncard := by
  classical
  have hAt : ∀ j i, 0 < Function.swap A j i := fun j i => hA i j
  have hndB : ∀ x, InPoly B x → (lab B x).card ≤ Fintype.card M := fun x hx =>
    card_lab_le h.1 hx
  have hndA : ∀ y, InPoly (Function.swap A) y → (lab (Function.swap A) y).card ≤ Fintype.card N :=
    fun y hy => card_lab_le (fun y => (bestResponses₂_swap A y).symm ▸ h.2 y) hy
  have hrecB := recession (ι := M) hB
  have hrecA := recession (ι := N) hAt
  -- equilibria have exactly `card M` and `card N` labels
  have hcardNash : ∀ x y, IsBimatrixNash A B x y →
      (labS B x).card = Fintype.card M ∧
        (lab (Function.swap A) (toPoly (Function.swap A) y)).card = Fintype.card N := by
    intro x y hxy
    have hU := (isBimatrixNash_iff_union hA hB x y).1 hxy
    have h1 := hndB _ (inPoly_toPoly hB x)
    have h2 := hndA _ (inPoly_toPoly hAt y)
    have h3 := card_union_le (labS B x) (labT A y)
    rw [hU, card_univ, Fintype.card_sum, labT, card_map, labS] at h3
    rw [labS]
    omega
  set VP : Finset (M ⊕ N) → Prop := VS B with hVP
  set VQ : Finset (M ⊕ N) → Prop :=
    fun T => VS (Function.swap A) (T.map (Equiv.sumComm M N).toEmbedding) with hVQ
  set CL := {q : Finset (M ⊕ N) × Finset (M ⊕ N) | VP q.1 ∧ VQ q.2 ∧ q.1 ∪ q.2 = univ}
    with hCL
  set F : StdSimplex ℝ M × StdSimplex ℝ N → Finset (M ⊕ N) × Finset (M ⊕ N) :=
    fun p => (labS B p.1, labT A p.2) with hF
  set q₀ : Finset (M ⊕ N) × Finset (M ⊕ N) :=
    (lab B 0, (lab (Function.swap A) 0).map (Equiv.sumComm N M).toEmbedding) with hq₀_def
  have hmapmap : ∀ U : Finset (N ⊕ M),
      (U.map (Equiv.sumComm N M).toEmbedding).map (Equiv.sumComm M N).toEmbedding = U := by
    intro U
    ext l
    simp
  -- the artificial equilibrium
  have hq₀ : q₀ ∈ CL := by
    refine ⟨⟨0, inPoly_zero, rfl, card_lab_zero⟩, ⟨0, inPoly_zero, (hmapmap _).symm, ?_⟩, ?_⟩
    · rw [hmapmap, card_lab_zero]
    · simp only [hq₀_def]
      refine eq_univ_of_forall fun l => ?_
      rcases l with i | j
      · exact mem_union_left _ (by simp [lab])
      · refine mem_union_right _ ?_
        rw [inr_mem_map_sumComm]
        simp [lab]
  -- parity of the completely labelled vertex pairs
  have heven : Even CL.ncard :=
    even_ncard_completelyLabeled (Sum.inl (Classical.arbitrary M))
      Fintype.card_sum.symm (fun S hS => hS.choose_spec.2.2)
      (fun T hT => by simpa using hT.choose_spec.2.2) (hasPivot_VS hrecB hndB)
      (hasPivot_map (Equiv.sumComm M N) (hasPivot_VS hrecA hndA))
  -- equilibria correspond to the other completely labelled vertex pairs
  have hinj : Set.InjOn F {p | IsBimatrixNash A B p.1 p.2} := by
    rintro ⟨x, y⟩ hxy ⟨x', y'⟩ _ heq
    simp only [hF, Prod.mk.injEq] at heq
    obtain ⟨hc1, hc2⟩ := hcardNash x y hxy
    have h1 : toPoly B x = toPoly B x' :=
      eq_of_lab_eq hrecB hndB (inPoly_toPoly hB x) hc1.ge heq.1
    have h2 : toPoly (Function.swap A) y = toPoly (Function.swap A) y' :=
      eq_of_lab_eq hrecA hndA (inPoly_toPoly hAt y) hc2.ge (map_injective _ heq.2)
    rw [toPoly_injective hB h1, toPoly_injective hAt h2]
  have himage : F '' {p | IsBimatrixNash A B p.1 p.2} = CL \ {q₀} := by
    ext ⟨S, T⟩
    simp only [Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      Prod.exists, hF, Prod.mk.injEq]
    constructor
    · rintro ⟨x, y, hxy, rfl, rfl⟩
      obtain ⟨hc1, hc2⟩ := hcardNash x y hxy
      refine ⟨⟨⟨_, inPoly_toPoly hB x, rfl, hc1⟩, ⟨_, inPoly_toPoly hAt y, ?_, ?_⟩,
        (isBimatrixNash_iff_union hA hB x y).1 hxy⟩, ?_⟩
      · rw [labT, hmapmap]
      · rw [labT, hmapmap, hc2]
      · intro hq
        obtain ⟨j, -, hj⟩ := univ.exists_max_image (fun j => ∑ i, x.weights i * B i j)
          univ_nonempty
        have hjBR : j ∈ bestResponses₂ B x := by
          simp only [bestResponses₂, mem_filter, mem_univ, true_and]
          exact fun j' => hj j' (mem_univ j')
        have hjS : Sum.inr j ∈ labS B x := (inr_mem_lab_toPoly hB x j).2 hjBR
        have hq1 := congrArg Prod.fst hq
        simp only [hq₀_def] at hq1
        rw [hq1] at hjS
        exact inr_notMem_lab_zero j hjS
    · rintro ⟨⟨⟨x, hx, rfl, -⟩, ⟨y, hy, hyT, -⟩, hU⟩, hne⟩
      have hT : T = (lab (Function.swap A) y).map (Equiv.sumComm N M).toEmbedding := by
        rw [hyT]
        ext l
        simp
      subst hT
      have hU' := eq_univ_iff_forall.1 hU
      have hx0 : x = 0 → y = 0 := by
        rintro rfl
        funext j
        have := hU' (Sum.inr j)
        rw [mem_union, inr_mem_map_sumComm] at this
        rcases this with h' | h'
        · exact absurd h' (inr_notMem_lab_zero j)
        · simpa [lab] using h'
      have hy0 : y = 0 → x = 0 := by
        rintro rfl
        funext i
        have := hU' (Sum.inl i)
        rw [mem_union, inl_mem_map_sumComm] at this
        rcases this with h' | h'
        · simpa [lab] using h'
        · exact absurd h' (inr_notMem_lab_zero i)
      have hxne : x ≠ 0 := by
        rintro rfl
        obtain rfl := hx0 rfl
        exact hne rfl
      have hyne : y ≠ 0 := fun h' => hxne (hy0 h')
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hxne
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hyne
      have hj' : Sum.inr j ∈ lab B x := by
        have := hU' (Sum.inr j)
        rw [mem_union, inr_mem_map_sumComm] at this
        exact this.resolve_right (by simpa [lab] using hj)
      have hi' : Sum.inr i ∈ lab (Function.swap A) y := by
        have := hU' (Sum.inl i)
        rw [mem_union, inl_mem_map_sumComm] at this
        exact this.resolve_left (by simpa [lab] using hi)
      obtain ⟨xh, rfl⟩ := exists_toPoly_eq hx hj'
      obtain ⟨yh, rfl⟩ := exists_toPoly_eq hy hi'
      exact ⟨xh, yh, (isBimatrixNash_iff_union hA hB xh yh).2 hU, rfl, rfl⟩
  have h1 := Set.ncard_sdiff_singleton_add_one hq₀ (Set.toFinite CL)
  rw [← himage, hinj.ncard_image] at h1
  rw [← h1] at heven
  exact Nat.not_even_iff_odd.1 (Nat.even_add_one.1 heven)

end Nash

section Shift

private lemma bilinPayoff_add_const (C : M → N → ℝ) (c : ℝ) (x : StdSimplex ℝ M)
    (y : StdSimplex ℝ N) : bilinPayoff (fun i j => C i j + c) x y = bilinPayoff C x y + c := by
  simp only [bilinPayoff, mul_add, add_mul, sum_add_distrib, ← mul_sum, ← sum_mul,
    StdSimplex.total_of_fintype, mul_one, one_mul]

private lemma bestResponses₁_add_const (A : M → N → ℝ) (c : ℝ) (y : StdSimplex ℝ N) :
    bestResponses₁ (fun i j => A i j + c) y = bestResponses₁ A y := by
  ext i
  simp only [bestResponses₁, mem_filter, mem_univ, true_and, add_mul, sum_add_distrib, ← mul_sum,
    StdSimplex.total_of_fintype, mul_one, add_le_add_iff_right]

private lemma bestResponses₂_add_const (B : M → N → ℝ) (c : ℝ) (x : StdSimplex ℝ M) :
    bestResponses₂ (fun i j => B i j + c) x = bestResponses₂ B x := by
  ext j
  simp only [bestResponses₂, mem_filter, mem_univ, true_and, mul_add, sum_add_distrib, ← sum_mul,
    StdSimplex.total_of_fintype, one_mul, add_le_add_iff_right]

end Shift

/-- **A nondegenerate bimatrix game has an odd number of Nash equilibria.** If both players
have at least one pure strategy and the game `(A, B)` is nondegenerate, then the set of Nash
equilibria `(x, y)` is finite and has odd cardinality. (`Set.ncard` of an infinite set is `0`,
so oddness of `ncard` includes finiteness.)

Source: B. von Stengel, "Equilibrium computation for two-player games in strategic and
extensive form", *Algorithmic Game Theory* (Cambridge University Press 2007), Corollary 3.7,
proved by the Lemke–Howson path-following argument (Algorithm 3.6; C. E. Lemke and
J. T. Howson, J. SIAM 12 (1964), 413–423). -/
theorem odd_ncard_isBimatrixNash [Nonempty M] [Nonempty N] (A B : M → N → ℝ)
    (h : IsNondegenerate A B) :
    Odd {p : StdSimplex ℝ M × StdSimplex ℝ N | IsBimatrixNash A B p.1 p.2}.ncard := by
  -- Adding a constant to all payoffs changes neither the equilibria nor the best responses;
  -- choose it so that all payoffs become positive.
  set c : ℝ := 1 + ∑ i, ∑ j, (|A i j| + |B i j|) with hc
  have hle : ∀ i j, |A i j| + |B i j| ≤ ∑ i, ∑ j, (|A i j| + |B i j|) := fun i j =>
    (single_le_sum (f := fun j => |A i j| + |B i j|) (fun j _ => by positivity)
      (mem_univ j)).trans (single_le_sum (f := fun i => ∑ j, (|A i j| + |B i j|))
        (fun i _ => sum_nonneg fun j _ => by positivity) (mem_univ i))
  have hA : ∀ i j, 0 < A i j + c := fun i j => by
    have := hle i j
    have := neg_abs_le (A i j)
    have := abs_nonneg (B i j)
    linarith
  have hB : ∀ i j, 0 < B i j + c := fun i j => by
    have := hle i j
    have := neg_abs_le (B i j)
    have := abs_nonneg (A i j)
    linarith
  have hset : {p : StdSimplex ℝ M × StdSimplex ℝ N | IsBimatrixNash A B p.1 p.2} =
      {p | IsBimatrixNash (fun i j => A i j + c) (fun i j => B i j + c) p.1 p.2} := by
    ext p
    simp only [Set.mem_ofPred_eq, IsBimatrixNash, bilinPayoff_add_const, add_le_add_iff_right]
  rw [hset]
  refine odd_ncard_of_pos _ _ hA hB ⟨fun x => ?_, fun y => ?_⟩
  · rw [bestResponses₂_add_const]
    exact h.1 x
  · rw [bestResponses₁_add_const]
    exact h.2 y

end MathlibExt.GameTheory.LemkeHowsonWanted

