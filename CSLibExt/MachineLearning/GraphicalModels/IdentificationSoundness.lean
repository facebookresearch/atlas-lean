/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CComponentCriterion
public import CSLibExt.MachineLearning.GraphicalModels.IdentificationAlgorithm
public import MathlibExt.Probability.FiniteWeight
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Soundness of the ID algorithm

Let `b` be a Bayesian network with a set `L` of latent nodes, `G` its latent projection onto the
observed nodes, `σ` a topological order of `G`, and `X`, `Y` disjoint sets of observed nodes. If
the identification algorithm `ADMG.ID` (Shpitser and Pearl, AAAI 2006, Fig. 3, lines 1-7)
returns an expression `e` for the effect `P_x(y)` and the observed law of `b` is strictly
positive, then `e`, evaluated against the observed law, equals `P_x(y)` at every observed
assignment. This is Theorem 5 of Shpitser and Pearl (AAAI 2006): "Whenever ID returns an
expression for P_x(y), it is correct." The effect `P_x(y)` is `BayesNet.doMarginal`: the
probability that the observed nodes of `Y` take the values `y` after `do(X = x)` on the observed
nodes of `X`, the latent nodes summed out, with `x` and `y` read off one full observed
assignment.

## Main definitions

* `BayesNet.doMarginal L X Y v` (defined with `observedLaw` and `qFactor` in
  `CComponentFactorization`): the effect `P_x(y)` at the observed assignment `v`.

## Main results

* `BayesNet.ID_sound`: soundness of `ADMG.ID` for every finite network with latent set `L`.
* `BayesNet.ID_sound_of_mem_tianClass`: the same on `BayesNet.tianClass L G`, the networks
  whose latent projection is `G`, whose observed law is strictly positive, and in which no
  latent node is a descendant of an observed node (Tian and Pearl's 2002 semi-Markovian
  hypothesis, which the exogenous background variables of the AAAI 2006 source satisfy);
  `BayesNet.ID_sound` needs no such hypothesis at all.
* `BayesNet.identifiedOn_doMarginal_of_ID_eq_ok`: a successful run of `ADMG.ID` identifies
  `P_x(y)` from the observed law on that class (`IdentifiedOn`).
* `BayesNet.idRec_sound`: the invariant behind these results: a call of `ADMG.idRec` on a vertex
  set `D` whose current law evaluates to the Q-factor `Q[D]` returns an expression for
  `Σ_{(D ∖ X) ∖ Y} Q[D ∖ X]`, the effect of `do(X)` on `Y` in the sub-model on `D`.
* The line identities `BayesNet.marginal_qFactor_restrict` (lines 2 and 3),
  `BayesNet.qFactor_eq_prod_cComponentsIn` (line 4) and `BayesNet.condChain_eval_qFactor`
  (lines 6 and 7), and `BayesNet.doMarginal_eq_marginal_qFactor`, which writes `P_x(y)` as
  `Σ_{(V ∖ X) ∖ Y} Q[V ∖ X]`.
* `IdExpr.eval_prodList` and `ADMG.condChain_eval`: how the products and conditional chains
  that ID returns evaluate.

## Hypotheses and scope

* `σ` is a topological order of the latent projection (the source's `π`), `X` and `Y` are
  disjoint (part of the source's definition of the effect, Definition 2), and the observed law is
  strictly positive at every assignment. The source (p. 1220) does not assume a positive law; it
  asks for two conditions instead: every conditioning event it uses has positive probability, and
  `P(x | Pa(X) ∖ X) > 0` for every action `do(x)` it considers, without which `P_x` is not well
  defined. Strict positivity of the observed law implies both, so the hypothesis here is
  stronger. Without positivity, or without a topological order, the conclusion fails. For the
  chain `X → Y` in which `X` is constant, `ADMG.ID` returns `P(y | x)`, which evaluates to `0`
  (real division by `0`) at the other value of `X`, while `P_x(y)` is the table entry of `Y` at
  `x`, which need not be `0`. For the chain `X → Y` with a fair `X` and `σ` listing `Y` before
  `X`, line 6 returns `P(y)` in place of `P(y | x)`, which differs from `P_x(y)` whenever `Y`
  depends on `X`.
* All variables, latent or observed, take values in one finite type `α`; the source allows a
  finite domain for each variable.
* `BayesNet.ID_sound` holds for every finite network with latent set `L` whose latent projection
  is the input graph, with no semi-Markovian hypothesis. `BayesNet.ID_sound_of_mem_tianClass`
  specializes it to `tianClass`, whose extra condition (no latent node a descendant of an
  observed node) is Tian and Pearl's 2002 semi-Markovian hypothesis (AAAI-02, p. 568). The
  models of the AAAI 2006 source satisfy it, since their unobservable variables, distributed by
  `P(U)`, are not determined by any other variable (p. 1220). The stronger normal form in which
  each latent node is a root with exactly two observed children is the convention of Tian and
  Pearl's technical report R-290-L (p. 6), not of the AAAI 2006 source.
* Failure outputs carry no claim. When `ADMG.ID` returns `.error (F, F')` (line 5), nothing is
  stated: neither that `(F, F')` is a hedge nor that `P_x(y)` is not identified. Completeness
  (Theorem 6 and Corollary 2 of the source) is not formalized; the test file shows a run that
  fails on the bow graph.

## Proof route

Every line is justified by c-component (Q-factor) factorization alone, through the identities of
`CComponentFactorization` (Tian and Pearl 2002, and Lemmas 3 and 4 of its companion technical
report R-290-L); no rule of the do-calculus is used. The source proves line 3 (Lemma 6) by rule 3
of the do-calculus; here line 3 is the ancestral marginalization
`BayesNet.marginal_qFactor_of_ancestral` inside `D ∖ X`.

## References

* I. Shpitser and J. Pearl, *Identification of Joint Interventional Distributions in Recursive
  Semi-Markovian Causal Models*, Proceedings of the Twenty-First National Conference on
  Artificial Intelligence (AAAI-06), AAAI Press (2006), 1219–1226. Locators in this file use the
  numbering of these proceedings. The result is Theorem 5 (p. 1225) with Lemmas 3–8 (p. 1224):
  Lemma 3 (termination), Lemma 4 (line 4), Lemma 5 (line 2), Lemma 6 (line 3), Lemma 7 (line 6)
  and Lemma 8 (line 7); the proof of Theorem 5 adds the base case of line 1. The causal model,
  finite domains, the positivity convention and the submodel `M_x` are set out in prose on
  pp. 1220–1221; Definition 2 (p. 1221) defines the identifiability of an effect, and Theorem 2
  (p. 1221) is the bow arc graph. The UCLA Cognitive Systems Laboratory technical report R-327
  of the same paper numbers differently: its Definitions 1–3 are the causal model, the submodel
  and identifiability, its Theorem 1 is the bow arc graph, and its Lemmas 2–6 (pp. 5–6) cover
  termination and lines 4, 2, 3 and 7, with line 6 in the proof of Theorem 5. Fig. 3 and
  Theorem 5 agree in both.
* I. Shpitser and J. Pearl, *Identification of Conditional Interventional Distributions*,
  Proceedings of the Twenty-Second Conference on Uncertainty in Artificial Intelligence
  (UAI-06), AUAI Press (2006), 437–444; technical report R-329. Section 4 (pp. 3–4) restates the
  result without proof; Sections 1–3 supply only notation, the positivity convention and the
  definition of identifiability.
* J. Tian and J. Pearl, *A General Identification Condition for Causal Effects*, Proceedings of
  the Eighteenth National Conference on Artificial Intelligence (AAAI-02), AAAI Press (2002),
  567–573, with its companion technical report R-290-L, for the Q-factor identities.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

namespace IdExpr

variable {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]

/-- **Evaluating a product of ID expressions.** For finite types `V` and `α` and a real-valued
weight `p` on the assignments `x : V → α`, the product `IdExpr.prodList l` of a list `l` of
expressions evaluates at `x` to the product of the evaluations at `x` of the members of `l` (the
empty product being `1`). -/
theorem eval_prodList (p : (V → α) → ℝ) (l : List (IdExpr V)) (x : V → α) :
    (IdExpr.prodList l).eval p x = (l.map fun e => e.eval p x).prod := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      change e.eval p x * (prodList l).eval p x = _
      rw [ih, List.map_cons, List.prod_cons]

end IdExpr

namespace ADMG

open MetaMathlibExt.FiniteWeight

universe u

variable {V : Type*} [Fintype V] [DecidableEq V] (G : ADMG V)
  (σ : V ≃ Fin (Fintype.card V))

/-! ### Evaluating the outputs of lines 4, 6 and 7 -/

/-- **Evaluating the conditional chain of lines 6 and 7 of ID.** Let `V` and `α` be finite
types, `p` a real-valued weight on the assignments `x : V → α`, `σ` an order of `V`, `D` and `S`
vertex sets and `P` an expression, and write `q` for the evaluation of `P` against `p`. The
conditional chain `condChain σ D S P` of lines 6 and 7 of ID (Shpitser and Pearl, AAAI 2006,
Fig. 3) evaluates at `x` to the product over `i ∈ S` of the ratios `q(v_i, v_{<i}) / q(v_{<i})`,
where `v_{<i}` are the vertices of `D` before `i` in `σ` and each term is the marginal of `q` that
fixes those vertices, and every vertex outside `D`, at their values in `x`. A ratio with
denominator `0` is `0` (real division). -/
theorem condChain_eval {α : Type*} [Fintype α] (D S : Finset V) (P : IdExpr V)
    (p : (V → α) → ℝ) (x : V → α) :
    (condChain σ D S P).eval p x = ∏ i ∈ S,
      marginal (P.eval p) (↑({i} ∪ D.filter fun u => σ u < σ i) ∪ (↑D)ᶜ) x /
        marginal (P.eval p) (↑(D.filter fun u => σ u < σ i) ∪ (↑D)ᶜ) x := by
  rw [condChain, IdExpr.eval_prodList, List.map_map, Finset.prod_map_toList]
  apply Finset.prod_congr rfl
  intro i _
  rfl

/-- The `do` block of line 4 of ID returns an expression only through a successful first step:
if `m >>= fun b => pure (g b)` is `.ok e`, then `m` is `.ok b` for some `b` with `e = g b`. -/
private theorem exists_of_bind_pure_eq_ok {ε : Type*} {β γ : Type u} {m : Except ε β} {g : β → γ}
    {e : γ} (h : (m >>= fun b => pure (g b)) = Except.ok e) : ∃ b, m = .ok b ∧ e = g b := by
  cases m with
  | error err => simp at h
  | ok b => exact ⟨b, rfl, by simpa using h.symm⟩

/-! ### Ancestral sets and c-components inside a vertex set -/

omit [Fintype V] [DecidableEq V] in
/-- The ancestral set `An(Y)` of `G[D]` used by line 2 of ID lies in `D`. -/
private theorem ancIn_subset (D Y : Finset V) : G.ancIn D Y ⊆ D := by
  classical
  unfold ancIn
  exact Finset.filter_subset _ _

omit [Fintype V] [DecidableEq V] in
/-- The ancestral set `An(Y)` of `G[D]` (line 2 of ID) is closed under the parents in `D` of its
vertices. -/
private theorem ancIn_closed {D Y : Finset V} {u w : V} (huw : G.dir u w) (hu : u ∈ D)
    (hw : w ∈ G.ancIn D Y) : u ∈ G.ancIn D Y := by
  classical
  unfold ancIn at hw ⊢
  simp only [Finset.mem_filter] at hw ⊢
  obtain ⟨hwD, y, hyY, hchain⟩ := hw
  exact ⟨hu, y, hyY, Relation.ReflTransGen.head ⟨hu, hwD, huw⟩ hchain⟩

omit [Fintype V] [DecidableEq V] in
/-- The ancestral set `An(Y)` of `G[D]` with the arrows into `X` deleted (line 3 of ID) is
closed under the parents in `D` of its vertices outside `X`. -/
private theorem ancCut_closed {D X Y : Finset V} {u w : V} (huw : G.dir u w) (hu : u ∈ D)
    (hw : w ∈ G.ancCut D X Y) (hwX : w ∉ X) : u ∈ G.ancCut D X Y := by
  classical
  unfold ancCut at hw ⊢
  simp only [Finset.mem_filter] at hw ⊢
  obtain ⟨hwD, y, hyY, hchain⟩ := hw
  exact ⟨hu, y, hyY, Relation.ReflTransGen.head ⟨⟨hu, hwD, huw⟩, hwX⟩ hchain⟩

omit [Fintype V] in
/-- No bidirected edge joins a c-component of `G[H]` (Shpitser and Pearl, AAAI 2006,
Definition 3) to the rest of `H`. -/
private theorem not_adj_of_mem_cComponentsIn {H S : Finset V} (hS : S ∈ G.cComponentsIn H)
    {u w : V} (hu : u ∈ S) (hw : w ∈ H \ S) : ¬ G.bidir.Adj u w := by
  classical
  rw [cComponentsIn, Finset.mem_image] at hS
  obtain ⟨v, hvH, hSv⟩ := hS
  rw [Finset.mem_sdiff] at hw
  obtain ⟨hwH, hwS⟩ := hw
  have hu' : u ∈ G.compIn H v := by
    rw [hSv]
    exact hu
  have huH : u ∈ H := by
    have h := hu'
    unfold compIn at h
    rw [Finset.mem_filter] at h
    exact h.1
  have huv : (G.induce ↑H).bidir.Reachable v u := by
    have h := hu'
    unfold compIn at h
    rw [Finset.mem_filter] at h
    exact (G.induce ↑H).mem_cComponent_iff.mp h.2
  intro hadj
  have hne : u ≠ w := G.bidir.ne_of_adj hadj
  have hadjI : (G.induce ↑H).bidir.Adj u w := by
    have hEq : (G.induce ↑H).bidir
        = SimpleGraph.fromRel fun a b => a ∈ (↑H : Set V) ∧ b ∈ ↑H ∧ G.bidir.Adj a b := rfl
    rw [hEq, SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl ⟨huH, hwH, hadj⟩⟩
  have hreach : (G.induce ↑H).bidir.Reachable u w := hadjI.reachable
  have hvw : (G.induce ↑H).bidir.Reachable v w := huv.trans hreach
  have hwv : w ∈ G.compIn H v := by
    unfold compIn
    rw [Finset.mem_filter]
    exact ⟨hwH, (G.induce ↑H).mem_cComponent_iff.mpr hvw⟩
  rw [hSv] at hwv
  exact hwS hwv

end ADMG

namespace BayesNet

open Finset MetaMathlibExt.FiniteWeight

variable {α : Type*} [Fintype α] [Nonempty α] {n : ℕ}
  (b : BayesNet α n) (L : Finset (Fin n))

/-! ### The lines of ID as Q-factor identities -/

/-- **Ancestral restriction of an effect.** Let a Bayesian network whose nodes take values in a
finite nonempty type have latent node set `L`, and let `A ⊆ H` and `Y` be sets of observed nodes
such that every parent in `H` of a node of `A`, in the latent projection, lies in `A`, and
`H ∩ Y ⊆ A`. Then at every observed assignment `v`, the sum of the Q-factor `Q[H]` over the
values of the nodes of `H ∖ Y` equals the sum of `Q[A]` over the values of the nodes of
`A ∖ Y`, the other nodes fixed at their values in `v`. This justifies lines 2 and 3 of ID
(Shpitser and Pearl, AAAI 2006, Lemmas 5 and 6) through Lemma 3 of Tian and Pearl's technical
report R-290-L, with no semi-Markovian hypothesis; the source proves line 3 by rule 3 of the
do-calculus instead. -/
theorem marginal_qFactor_restrict {H A Y : Finset {i : Fin n // i ∉ L}} (hAH : A ⊆ H)
    (hanc : ∀ ⦃u w⦄, (b.latentProjection L).dir u w → u ∈ H → w ∈ A → u ∈ A)
    (hYA : H ∩ Y ⊆ A) (v : {i : Fin n // i ∉ L} → α) :
    marginal (b.qFactor L H) (↑(H \ Y))ᶜ v = marginal (b.qFactor L A) (↑(A \ Y))ᶜ v := by
  let _ : DecidableEq α := fun a b => Classical.propDecidable (a = b)
  have hdisj : (↑(A \ Y) : Set {i : Fin n // i ∉ L}) ∩ (↑(H \ A) : Set {i : Fin n // i ∉ L})
      = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hxA, -⟩, -, hxA'⟩
      exact (hxA' hxA).elim
    · intro hx
      simp at hx
  have hunion : (↑(A \ Y) : Set {i : Fin n // i ∉ L})ᶜ ∪ (↑(H \ A) : Set {i : Fin n // i ∉ L})ᶜ
      = Set.univ := by
    rw [← Set.compl_inter, hdisj, Set.compl_empty]
  have hset : (↑(A \ Y) : Set {i : Fin n // i ∉ L}) ∪ (↑(H \ A) : Set {i : Fin n // i ∉ L})
      = (↑(H \ Y) : Set {i : Fin n // i ∉ L}) := by
    ext x
    simp only [Set.mem_union, Finset.mem_coe, Finset.mem_sdiff]
    constructor
    · rintro (⟨hxA, hxY⟩ | ⟨hxH, hxA⟩)
      · exact ⟨hAH hxA, hxY⟩
      · refine ⟨hxH, ?_⟩
        intro hxY
        exact hxA (hYA (Finset.mem_inter.mpr ⟨hxH, hxY⟩))
    · rintro ⟨hxH, hxY⟩
      by_cases hxA : x ∈ A
      · exact Or.inl ⟨hxA, hxY⟩
      · exact Or.inr ⟨hxH, hxA⟩
  have hinter : (↑(A \ Y) : Set {i : Fin n // i ∉ L})ᶜ ∩ (↑(H \ A) : Set {i : Fin n // i ∉ L})ᶜ
      = (↑(H \ Y) : Set {i : Fin n // i ∉ L})ᶜ := by
    rw [← Set.compl_union, hset]
  have hfun : marginal (b.qFactor L H) (↑(H \ A) : Set {i : Fin n // i ∉ L})ᶜ = b.qFactor L A :=
    funext (fun w => marginal_qFactor_of_ancestral b L hAH hanc w)
  calc marginal (b.qFactor L H) (↑(H \ Y) : Set {i : Fin n // i ∉ L})ᶜ v
        = marginal (b.qFactor L H)
          ((↑(A \ Y) : Set {i : Fin n // i ∉ L})ᶜ ∩ (↑(H \ A) : Set {i : Fin n // i ∉ L})ᶜ) v := by
          rw [hinter]
      _ = marginal (marginal (b.qFactor L H) (↑(H \ A) : Set {i : Fin n // i ∉ L})ᶜ)
          (↑(A \ Y) : Set {i : Fin n // i ∉ L})ᶜ v :=
          (marginal_marginal_of_union_eq_univ (b.qFactor L H) hunion v).symm
      _ = marginal (b.qFactor L A) (↑(A \ Y) : Set {i : Fin n // i ∉ L})ᶜ v := by rw [hfun]

/-- **C-component factorization inside a vertex set.** For a Bayesian network whose nodes take
values in a finite nonempty type, with latent node set `L`, a set `H` of observed nodes and an
observed assignment `v`, the Q-factor `Q[H](v)` is the product of the Q-factors `Q[S](v)` over
the c-components `S` of the subgraph of the latent projection induced on `H`. This is line 4 of
ID (Shpitser and Pearl, AAAI 2006, Lemma 4), with no semi-Markovian hypothesis. -/
theorem qFactor_eq_prod_cComponentsIn (H : Finset {i : Fin n // i ∉ L})
    (v : {i : Fin n // i ∉ L} → α) :
    b.qFactor L H v = ∏ S ∈ (b.latentProjection L).cComponentsIn H, b.qFactor L S v := by
  let _ : DecidableEq α := fun a b => Classical.propDecidable (a = b)
  have hpart := (b.latentProjection L).cComponentsIn_partition H
  refine qFactor_eq_prod_of_not_adj b L _ ?_ ?_ ?_ v
  · intro S hS T hT hST
    exact hpart.2.2.1 S (Finset.mem_coe.mp hS) T (Finset.mem_coe.mp hT) hST
  · exact hpart.2.2.2
  · intro T hT T' hT' hTT u hu w hw
    have hsub : T' ⊆ H := hpart.2.1 T' hT'
    have hdis : Disjoint T T' := hpart.2.2.1 T hT T' hT' hTT
    have hwT : w ∉ T := fun hh => (Finset.disjoint_left.mp hdis hh) hw
    have hwHS : w ∈ H \ T := Finset.mem_sdiff.mpr ⟨hsub hw, hwT⟩
    exact ADMG.not_adj_of_mem_cComponentsIn _ hT hu hwHS

/-- **The conditional chain of a c-component.** Let a Bayesian network whose nodes take values in
a finite nonempty type have latent node set `L`, let `σ` be a topological order of its latent
projection, let `S` be a c-component of the subgraph of the projection induced on a set `D` of
observed nodes, and let `P` be an expression that evaluates, against the observed law, to the
Q-factor `Q[D]` at every observed assignment. Then at every observed assignment `v` of positive
observed probability, the conditional chain of `P` over `S` along `σ` inside `D` (lines 6 and 7
of ID) evaluates to `Q[S](v)`. This covers Lemmas 7 and 8 of Shpitser and Pearl (AAAI 2006),
through Lemma 1 of Tian and Pearl (2002) applied in the subgraph on `D`. -/
theorem condChain_eval_qFactor
    {σ : {i : Fin n // i ∉ L} ≃ Fin (Fintype.card {i : Fin n // i ∉ L})}
    (hσ : ∀ ⦃u w⦄, (b.latentProjection L).dir u w → σ u < σ w)
    {D S : Finset {i : Fin n // i ∉ L}} (hS : S ∈ (b.latentProjection L).cComponentsIn D)
    {P : IdExpr {i : Fin n // i ∉ L}}
    (hP : ∀ w, P.eval (b.observedLaw L) w = b.qFactor L D w)
    {v : {i : Fin n // i ∉ L} → α} (hv : 0 < b.observedLaw L v) :
    (ADMG.condChain σ D S P).eval (b.observedLaw L) v = b.qFactor L S v := by
  let _ : DecidableEq α := fun a b => Classical.propDecidable (a = b)
  have hpart := (b.latentProjection L).cComponentsIn_partition D
  have hSD : S ⊆ D := hpart.2.1 S hS
  have hsep : ∀ u ∈ S, ∀ w ∈ D \ S, ¬ (b.latentProjection L).bidir.Adj u w :=
    fun u hu w hw => ADMG.not_adj_of_mem_cComponentsIn _ hS hu hw
  have hPfun : P.eval (b.observedLaw L) = b.qFactor L D := funext hP
  have hset : ∀ C : Finset {i : Fin n // i ∉ L},
      (↑C : Set {i : Fin n // i ∉ L}) ∪ (↑D : Set {i : Fin n // i ∉ L})ᶜ
        = (↑(D \ C) : Set {i : Fin n // i ∉ L})ᶜ := by
    intro C
    ext x
    simp only [Set.mem_union, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_sdiff]
    tauto
  have hsub1 : ∀ i ∈ S, ({i} ∪ D.filter (fun u => σ u < σ i)) ⊆ D := by
    intro i hi x hx
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter] at hx
    rcases hx with rfl | ⟨hxD, -⟩
    · exact hSD hi
    · exact hxD
  have hanc1 : ∀ i ∈ S, ∀ ⦃u w⦄, (b.latentProjection L).dir u w → u ∈ D →
      w ∈ ({i} ∪ D.filter (fun u => σ u < σ i)) → u ∈ ({i} ∪ D.filter (fun u => σ u < σ i)) := by
    intro i hi u w huw huD hw
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter] at hw ⊢
    have hlt : σ u < σ w := hσ huw
    rcases hw with rfl | ⟨-, hlt2⟩
    · exact Or.inr ⟨huD, hlt⟩
    · exact Or.inr ⟨huD, lt_trans hlt hlt2⟩
  have hsub0 : ∀ i : {i : Fin n // i ∉ L}, (D.filter (fun u => σ u < σ i)) ⊆ D :=
    fun i => Finset.filter_subset _ _
  have hanc0 : ∀ i : {i : Fin n // i ∉ L}, ∀ ⦃u w⦄, (b.latentProjection L).dir u w → u ∈ D →
      w ∈ D.filter (fun u => σ u < σ i) → u ∈ D.filter (fun u => σ u < σ i) := by
    intro i u w huw huD hw
    simp only [Finset.mem_filter] at hw ⊢
    exact ⟨huD, lt_trans (hσ huw) hw.2⟩
  have hfactor : ∀ i ∈ S,
      marginal (b.qFactor L D) (↑({i} ∪ D.filter (fun u => σ u < σ i)) ∪ (↑D)ᶜ) v /
        marginal (b.qFactor L D) (↑(D.filter (fun u => σ u < σ i)) ∪ (↑D)ᶜ) v =
        b.qFactor L ({i} ∪ D.filter (fun u => σ u < σ i)) v /
          b.qFactor L (D.filter (fun u => σ u < σ i)) v := by
    intro i hi
    rw [hset, hset,
      marginal_qFactor_of_ancestral b L (hsub1 i hi) (hanc1 i hi) v,
      marginal_qFactor_of_ancestral b L (hsub0 i) (hanc0 i) v]
  have hL4 := qFactor_mul_prod_qFactor_pred b L hSD hsep σ v
  have hpos : ∀ i ∈ S, 0 < b.qFactor L (D.filter (fun u => σ u < σ i)) v :=
    fun i _ => qFactor_pos b L hv _
  have hne : (∏ i ∈ S, b.qFactor L (D.filter (fun u => σ u < σ i)) v) ≠ 0 :=
    ne_of_gt (Finset.prod_pos hpos)
  calc (ADMG.condChain σ D S P).eval (b.observedLaw L) v
        = ∏ i ∈ S, (marginal (b.qFactor L D) (↑({i} ∪ D.filter (fun u => σ u < σ i)) ∪ (↑D)ᶜ) v /
          marginal (b.qFactor L D) (↑(D.filter (fun u => σ u < σ i)) ∪ (↑D)ᶜ) v) := by
          rw [ADMG.condChain_eval, hPfun]
      _ = ∏ i ∈ S, (b.qFactor L ({i} ∪ D.filter (fun u => σ u < σ i)) v /
          b.qFactor L (D.filter (fun u => σ u < σ i)) v) :=
          Finset.prod_congr rfl hfactor
      _ = (∏ i ∈ S, b.qFactor L ({i} ∪ D.filter (fun u => σ u < σ i)) v) /
          (∏ i ∈ S, b.qFactor L (D.filter (fun u => σ u < σ i)) v) :=
          Finset.prod_div_distrib _ _
      _ = b.qFactor L S v := by rw [← hL4, div_eq_iff hne]

private theorem ids_aux_sum_eval
    {H A : Finset {i : Fin n // i ∉ L}} {P : IdExpr {i : Fin n // i ∉ L}}
    (hAH : A ⊆ H)
    (hanc : ∀ ⦃u w⦄, (b.latentProjection L).dir u w → u ∈ H → w ∈ A → u ∈ A)
    (hP : ∀ w, P.eval (b.observedLaw L) w = b.qFactor L H w)
    (w : {i : Fin n // i ∉ L} → α) :
    (IdExpr.sum (H \ A) P).eval (b.observedLaw L) w = b.qFactor L A w := by
  have : DecidableEq α := fun a b => Classical.propDecidable (a = b)
  simp only [IdExpr.eval]
  have hPfun : P.eval (b.observedLaw L) = b.qFactor L H := funext hP
  rw [hPfun]
  exact marginal_qFactor_of_ancestral b L hAH hanc w

private theorem ids_aux_line4_elem
    {D S : Finset {i : Fin n // i ∉ L}} (hSD : S ⊆ D)
    (w : {i : Fin n // i ∉ L} → α) :
    marginal (b.qFactor L (D \ (D \ S))) (↑((D \ (D \ S)) \ S))ᶜ w
      = b.qFactor L S w := by
  have hDD : D \ (D \ S) = S := Finset.sdiff_sdiff_eq_self hSD
  rw [hDD, Finset.sdiff_self, Finset.coe_empty, Set.compl_empty]
  exact marginal_univ _ _

/-! ### The recursion invariant -/

/-- **The recursion invariant of ID.** Let a Bayesian network whose nodes take values in a finite
nonempty type have latent node set `L`, let `σ` be a topological order of its latent projection,
and suppose the observed law is strictly positive at every observed assignment. Let `D` be a set
of observed nodes, `X` and `Y` disjoint subsets of `D`, and `P` an expression that evaluates,
against the observed law, to the Q-factor `Q[D]` at every observed assignment. If the recursion
`idRec` of ID, called on `Y`, `X`, `D` and `P`, returns an expression `e`, then at every observed
assignment `v`, `e` evaluates to the sum of `Q[D ∖ X]` over the values of the nodes of
`(D ∖ X) ∖ Y`: the effect of `do(X)` on `Y` in the sub-model on `D`. Nothing is claimed when
`idRec` fails. This is the induction behind Theorem 5 of Shpitser and Pearl (AAAI 2006), with
their Lemmas 4, 5, 6 and 8 for the recursive calls. -/
theorem idRec_sound
    {σ : {i : Fin n // i ∉ L} ≃ Fin (Fintype.card {i : Fin n // i ∉ L})}
    (hσ : ∀ ⦃u w⦄, (b.latentProjection L).dir u w → σ u < σ w)
    (hpos : ∀ v, 0 < b.observedLaw L v)
    {Y X D : Finset {i : Fin n // i ∉ L}} {P e : IdExpr {i : Fin n // i ∉ L}}
    (hP : ∀ v, P.eval (b.observedLaw L) v = b.qFactor L D v)
    (hXD : X ⊆ D) (hYD : Y ⊆ D) (hXY : Disjoint X Y)
    (h : (b.latentProjection L).idRec σ Y X D P = .ok e) (v : {i : Fin n // i ∉ L} → α) :
    e.eval (b.observedLaw L) v = marginal (b.qFactor L (D \ X)) (↑((D \ X) \ Y))ᶜ v := by
  refine ADMG.idRec.induct (b.latentProjection L) σ
    (fun Y X D P =>
      ∀ (e : IdExpr {i : Fin n // i ∉ L}) (v : {i : Fin n // i ∉ L} → α)
        (hP : ∀ w, P.eval (b.observedLaw L) w = b.qFactor L D w)
        (hXD : X ⊆ D) (hYD : Y ⊆ D) (hXY : Disjoint X Y)
        (h : (b.latentProjection L).idRec σ Y X D P = Except.ok e),
        e.eval (b.observedLaw L) v
          = marginal (b.qFactor L (D \ X)) (↑((D \ X) \ Y))ᶜ v)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ Y X D P e v hP hXD hYD hXY h
  · intro Y D P e v hP hXD hYD hXY h
    rw [ADMG.idRec.eq_def, ite_eq_left rfl] at h
    simp only [Except.ok.injEq] at h
    subst h
    simp only [IdExpr.eval]
    have hPfun : P.eval (b.observedLaw L) = b.qFactor L D := funext hP
    rw [hPfun]
    simp only [Finset.sdiff_empty]
  · intro Y X D P hne hA ih e v hP hXD hYD hXY h
    rw [ADMG.idRec.eq_def, ite_eq_right hne, dite_eq_left hA] at h
    obtain ⟨⟨hXA, hYA, hXYA⟩, -, -, -, -⟩ :=
      ADMG.idRec_invariants (b.latentProjection L) hXD hYD hXY
    have hAD : (b.latentProjection L).ancIn D Y ⊆ D :=
      ADMG.ancIn_subset (b.latentProjection L) D Y
    have hP' : ∀ w, (IdExpr.sum (D \ (b.latentProjection L).ancIn D Y) P).eval
        (b.observedLaw L) w
        = b.qFactor L ((b.latentProjection L).ancIn D Y) w := by
      intro w
      exact ids_aux_sum_eval b L hAD
        (fun u w huw hu hw => ADMG.ancIn_closed (b.latentProjection L) huw hu hw) hP w
    have ih' := ih e v hP' hXA hYA hXYA h
    have hAX : (b.latentProjection L).ancIn D Y \ (X ∩ (b.latentProjection L).ancIn D Y)
        = (b.latentProjection L).ancIn D Y \ X := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    rw [ih', hAX]
    have hAH : (b.latentProjection L).ancIn D Y \ X ⊆ D \ X :=
      Finset.sdiff_subset_sdiff hAD (fun x hx => hx)
    have hanc : ∀ ⦃u w⦄, (b.latentProjection L).dir u w → u ∈ D \ X →
        w ∈ (b.latentProjection L).ancIn D Y \ X →
        u ∈ (b.latentProjection L).ancIn D Y \ X := by
      intro u w huw hu hw
      obtain ⟨huD, huX⟩ := Finset.mem_sdiff.mp hu
      obtain ⟨hwA, -⟩ := Finset.mem_sdiff.mp hw
      exact Finset.mem_sdiff.mpr
        ⟨ADMG.ancIn_closed (b.latentProjection L) huw huD hwA, huX⟩
    have hsub : (D \ X) ∩ Y ⊆ (b.latentProjection L).ancIn D Y \ X := by
      intro y hy
      obtain ⟨-, hyY⟩ := Finset.mem_inter.mp hy
      exact Finset.mem_sdiff.mpr ⟨hYA hyY, (Finset.disjoint_right.mp hXY) hyY⟩
    exact (marginal_qFactor_restrict b L hAH hanc hsub v).symm
  · intro Y X D P hne hA' hW ih e v hP hXD hYD hXY h
    rw [ADMG.idRec.eq_def, ite_eq_right hne, dite_eq_right hA', dite_eq_left hW] at h
    obtain ⟨-, ⟨hXD', hYD', hXY'⟩, -, -, -⟩ :=
      ADMG.idRec_invariants (b.latentProjection L) hXD hYD hXY
    have ih' := ih e v hP hXD' hYD' hXY' h
    have hDW : D \ (X ∪ (D \ X) \ (b.latentProjection L).ancCut D X Y)
        = (D \ X) \ ((D \ X) \ (b.latentProjection L).ancCut D X Y) := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [ih', hDW]
    have hAH : (D \ X) \ ((D \ X) \ (b.latentProjection L).ancCut D X Y) ⊆ D \ X :=
      Finset.sdiff_subset
    have hanc : ∀ ⦃u w⦄, (b.latentProjection L).dir u w → u ∈ D \ X →
        w ∈ (D \ X) \ ((D \ X) \ (b.latentProjection L).ancCut D X Y) →
        u ∈ (D \ X) \ ((D \ X) \ (b.latentProjection L).ancCut D X Y) := by
      intro u w huw hu hw
      obtain ⟨huD, -⟩ := Finset.mem_sdiff.mp hu
      obtain ⟨hwDX, hwW⟩ := Finset.mem_sdiff.mp hw
      have hwC : w ∈ (b.latentProjection L).ancCut D X Y := by
        by_contra hwC
        exact hwW (Finset.mem_sdiff.mpr ⟨hwDX, hwC⟩)
      have hwX : w ∉ X := (Finset.mem_sdiff.mp hwDX).2
      have huC : u ∈ (b.latentProjection L).ancCut D X Y :=
        ADMG.ancCut_closed (b.latentProjection L) huw huD hwC hwX
      exact Finset.mem_sdiff.mpr ⟨hu, fun huW => (Finset.mem_sdiff.mp huW).2 huC⟩
    have hsub : (D \ X) ∩ Y
        ⊆ (D \ X) \ ((D \ X) \ (b.latentProjection L).ancCut D X Y) := by
      intro y hy
      obtain ⟨hyDX, hyY⟩ := Finset.mem_inter.mp hy
      have hyC : y ∈ (b.latentProjection L).ancCut D X Y :=
        ADMG.subset_ancCut (b.latentProjection L) hYD hyY
      exact Finset.mem_sdiff.mpr ⟨hyDX, fun hyW => (Finset.mem_sdiff.mp hyW).2 hyC⟩
    exact (marginal_qFactor_restrict b L hAH hanc hsub v).symm
  · intro Y X D P hne hA' hW' hT ih e v hP hXD hYD hXY h
    rw [ADMG.idRec.eq_def, ite_eq_right hne, dite_eq_right hA', dite_eq_right hW',
      dite_eq_left hT] at h
    obtain ⟨es', hmap, he⟩ := ADMG.exists_of_bind_pure_eq_ok h
    subst he
    simp only [List.mapM_eq_ok_iff_forall₂] at hmap
    have key : ∀ (w : {i : Fin n // i ∉ L} → α)
        (l : List {S : Finset {i : Fin n // i ∉ L} //
          S ∈ ((b.latentProjection L).cComponentsIn (D \ X)).toList})
        (es : List (IdExpr {i : Fin n // i ∉ L})),
        List.Forall₂
          (fun (S : {S : Finset {i : Fin n // i ∉ L} //
              S ∈ ((b.latentProjection L).cComponentsIn (D \ X)).toList})
            (e : IdExpr {i : Fin n // i ∉ L}) =>
            (b.latentProjection L).idRec σ ↑S (D \ ↑S) D P = .ok e) l es →
        (es.map fun e => e.eval (b.observedLaw L) w).prod
          = (l.map fun (S : {S : Finset {i : Fin n // i ∉ L} //
            S ∈ ((b.latentProjection L).cComponentsIn (D \ X)).toList}) =>
            b.qFactor L ↑S w).prod := by
      intro w l
      induction l with
      | nil =>
        intro es h
        cases h
        rfl
      | cons hd tl ihl =>
        intro es h
        cases es with
        | nil => cases h
        | cons e_hd e_tl =>
          rw [List.forall₂_cons] at h
          obtain ⟨hhd, htl⟩ := h
          have hSmem : (↑hd : Finset {i : Fin n // i ∉ L})
              ∈ (b.latentProjection L).cComponentsIn (D \ X) :=
            Finset.mem_toList.mp hd.2
          obtain ⟨h1', h2', h3'⟩ :=
            (ADMG.idRec_invariants (b.latentProjection L) hXD hYD hXY).2.2.1 _ hSmem
          have ihd := ih hd e_hd w hP h1' h2' h3' hhd
          have hhd_eval : e_hd.eval (b.observedLaw L) w = b.qFactor L ↑hd w := by
            rw [ihd]
            exact ids_aux_line4_elem b L h2' w
          simp only [List.map_cons, List.prod_cons, hhd_eval, ihl _ htl]
    have hE : ∀ w, (IdExpr.prodList es').eval (b.observedLaw L) w
        = ((b.latentProjection L).cComponentsIn (D \ X)).prod
          fun S => b.qFactor L S w := by
      intro w
      rw [IdExpr.eval_prodList, key w _ _ hmap]
      have hatt : List.map
          (fun (S : {S : Finset {i : Fin n // i ∉ L} //
            S ∈ ((b.latentProjection L).cComponentsIn (D \ X)).toList}) =>
            b.qFactor L ↑S w)
          (((b.latentProjection L).cComponentsIn (D \ X)).toList.attach)
          = List.map (fun S => b.qFactor L S w)
          (((b.latentProjection L).cComponentsIn (D \ X)).toList) :=
        List.attach_map_val
          (l := ((b.latentProjection L).cComponentsIn (D \ X)).toList)
          (f := fun S => b.qFactor L S w)
      rw [hatt, Finset.prod_map_toList]
    have hEfun : (IdExpr.prodList es').eval (b.observedLaw L) = b.qFactor L (D \ X) :=
      funext fun w => by
        rw [hE w]
        exact (b.qFactor_eq_prod_cComponentsIn L (D \ X) w).symm
    have hset : D \ (Y ∪ X) = (D \ X) \ Y := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    simp only [IdExpr.eval]
    rw [hset, hEfun]
  · intro Y X D P hne hA' hW' hT' hD e v hP hXD hYD hXY h
    rw [ADMG.idRec.eq_def, ite_eq_right hne, dite_eq_right hA', dite_eq_right hW',
      dite_eq_right hT',
      dite_eq_left hD] at h
    simp at h
  · intro Y X D P hne hA' hW' hT' hD' h6 e v hP hXD hYD hXY h
    rw [ADMG.idRec.eq_def, ite_eq_right hne, dite_eq_right hA', dite_eq_right hW',
      dite_eq_right hT', dite_eq_right hD',
      ite_eq_left h6] at h
    simp only [Except.ok.injEq] at h
    subst h
    have hcond : (ADMG.condChain σ D (D \ X) P).eval (b.observedLaw L)
        = b.qFactor L (D \ X) :=
      funext fun w => condChain_eval_qFactor b L hσ h6 hP (hpos w)
    simp only [IdExpr.eval]
    rw [hcond]
  · intro Y X D P hne hA' hW' hT' hD' h6' hne7 S' ih e v hP hXD hYD hXY h
    rw [ADMG.idRec.eq_def, ite_eq_right hne, dite_eq_right hA', dite_eq_right hW',
      dite_eq_right hT', dite_eq_right hD',
      ite_eq_right h6'] at h
    dsimp only at h
    have hmem : D \ X ∈ (b.latentProjection L).cComponentsIn (D \ X) := of_not_not hT'
    have hchoose_mem : hne7.choose ∈ D \ X := hne7.choose_spec
    have hsub : D \ X ⊆ S' :=
      ADMG.line7_compIn_subset (b.latentProjection L) hmem hchoose_mem
    have hSsub : S' ⊆ D :=
      ADMG.compIn_subset (b.latentProjection L) D hne7.choose
    have hSmem : S' ∈ (b.latentProjection L).cComponentsIn D := by
      simp only [ADMG.cComponentsIn, Finset.mem_image]
      exact ⟨hne7.choose, Finset.sdiff_subset hchoose_mem, rfl⟩
    have hP' : ∀ w, (ADMG.condChain σ D S' P).eval (b.observedLaw L) w
        = b.qFactor L S' w :=
      fun w => condChain_eval_qFactor b L hσ hSmem hP (hpos w)
    obtain ⟨hXA, hYA, hXYA⟩ :=
      (ADMG.idRec_invariants (b.latentProjection L) hXD hYD hXY).2.2.2.1 hmem _ hchoose_mem
    have ih' := ih e v hP' hXA hYA hXYA h
    have hAX : S' \ (X ∩ S') = S' \ X := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    have hDXsub : D \ X ⊆ S' \ X := by
      intro a ha
      obtain ⟨-, haX⟩ := Finset.mem_sdiff.mp ha
      exact Finset.mem_sdiff.mpr ⟨hsub ha, haX⟩
    have hSeq : S' \ X = D \ X :=
      le_antisymm (Finset.sdiff_subset_sdiff hSsub (fun x hx => hx)) hDXsub
    rw [ih', hAX, hSeq]

/-! ### Soundness of ID -/

omit [Fintype α] in
private theorem ids_aux_extendObs_apply (w : {i : Fin n // i ∉ L} → α)
    (u : {i : Fin n // i ∉ L}) : extendObs L w (u : Fin n) = w u := by
  unfold extendObs
  rw [dite_eq_right u.2]

/-- **The effect as a marginal of a Q-factor.** For a Bayesian network whose nodes take values in
a finite nonempty type, with latent node set `L`, sets `X` and `Y` of observed nodes and an
observed assignment `v`, the effect `P_x(y)` read at `v` equals the sum of the Q-factor
`Q[O ∖ X]` over the values of the nodes of `(O ∖ X) ∖ Y`, the other observed nodes fixed at
their values in `v`, where `O` is the set of all observed nodes. No disjointness of `X` and `Y`
is assumed. -/
theorem doMarginal_eq_marginal_qFactor (X Y : Finset {i : Fin n // i ∉ L})
    (v : {i : Fin n // i ∉ L} → α) :
    b.doMarginal L X Y v = marginal (b.qFactor L (univ \ X)) (↑((univ \ X) \ Y))ᶜ v := by
  classical
  have hSX : (univ \ X)ᶜ = X := by
    ext u
    simp only [Finset.mem_compl, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
  have hqfactor_eq : ∀ (o : {i : Fin n // i ∉ L} → α),
      b.qFactor L (univ \ X) o =
        (∑ z ∈ univ.filter (fun z : Fin n → α =>
          ∀ i ∈ (↑((univ \ X).map (Function.Embedding.subtype _)) : Set (Fin n)),
          z i = extendObs L o i),
          (b.mutilateSet (X.map (Function.Embedding.subtype _)) (extendObs L o)).joint z) := by
    intro o
    simp only [qFactor, marginal, hSX]
    rw [Finset.filter_congr_decidable _ (fun z : Fin n → α =>
      ∀ i ∈ (↑((univ \ X).map (Function.Embedding.subtype _)) : Set (Fin n)),
      z i = extendObs L o i) _]
  simp only [doMarginal, marginal]
  simp only [hqfactor_eq]
  rw [Finset.filter_congr_decidable _ (fun z : Fin n → α =>
    ∀ i ∈ (↑(Y.map (Function.Embedding.subtype _)) : Set (Fin n)),
    z i = extendObs L v i) _]
  rw [Finset.filter_congr_decidable _ (fun o : {i : Fin n // i ∉ L} → α =>
    ∀ w ∈ ((↑((univ \ X) \ Y) : Set {i : Fin n // i ∉ L}))ᶜ, o w = v w) _]
  change (∑ z ∈ univ.filter (fun z : Fin n → α =>
      ∀ i ∈ (↑(Y.map (Function.Embedding.subtype _)) : Set (Fin n)),
      z i = extendObs L v i),
      (b.mutilateSet (X.map (Function.Embedding.subtype _)) (extendObs L v)).joint z) =
    (∑ o ∈ univ.filter (fun o : {i : Fin n // i ∉ L} → α =>
      ∀ w ∈ ((↑((univ \ X) \ Y) : Set {i : Fin n // i ∉ L}))ᶜ,
      o w = v w),
      ∑ z ∈ univ.filter (fun z : Fin n → α =>
        ∀ i ∈ (↑((univ \ X).map (Function.Embedding.subtype _)) : Set (Fin n)),
        z i = extendObs L o i),
        (b.mutilateSet (X.map (Function.Embedding.subtype _)) (extendObs L o)).joint z)
  have hcorr : ∀ (o : {i : Fin n // i ∉ L} → α) (z : Fin n → α),
      (o ∈ univ.filter (fun o : {i : Fin n // i ∉ L} → α =>
          ∀ w ∈ ((↑((univ \ X) \ Y) : Set {i : Fin n // i ∉ L}))ᶜ,
          o w = v w) ∧
        z ∈ univ.filter (fun z : Fin n → α =>
          ∀ i ∈ (↑((univ \ X).map (Function.Embedding.subtype _)) : Set (Fin n)),
          z i = extendObs L o i)) ↔
        (o ∈ ({(fun u : {i : Fin n // i ∉ L} => if u ∈ X then v u else z (u : Fin n))} :
            Finset ({i : Fin n // i ∉ L} → α)) ∧
          z ∈ univ.filter (fun z : Fin n → α =>
            ∀ i ∈ (↑((Y \ X).map (Function.Embedding.subtype _)) : Set (Fin n)),
            z i = extendObs L v i)) := by
    intro o z
    constructor
    · rintro ⟨ho, hz⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ho hz
      constructor
      swap
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro i hi
        simp only [Finset.mem_coe, Finset.mem_map, Function.Embedding.subtype_apply] at hi
        obtain ⟨w, hw, rfl⟩ := hi
        have hwY : w ∈ Y := (Finset.mem_sdiff.mp hw).1
        have hwX : w ∉ X := (Finset.mem_sdiff.mp hw).2
        have hwS : w ∈ univ \ X := Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hwX⟩
        have h1 : z (w : Fin n) = extendObs L o (w : Fin n) :=
          hz _ (Finset.mem_coe.mpr ((Finset.mem_map' (Function.Embedding.subtype _)).mpr hwS))
        have hwC : w ∈ ((↑((univ \ X) \ Y) : Set {i : Fin n // i ∉ L}))ᶜ := by
          change w ∉ (↑((univ \ X) \ Y) : Set {i : Fin n // i ∉ L})
          simp only [Finset.mem_coe, Finset.mem_sdiff]
          intro hcon
          exact absurd hwY hcon.2
        have h2 : o w = v w := ho w hwC
        rw [h1, ids_aux_extendObs_apply L o w, h2, ids_aux_extendObs_apply L v w]
      · simp only [Finset.mem_singleton]
        funext u
        by_cases huX : u ∈ X
        · have huC : u ∈ ((↑((univ \ X) \ Y) : Set {i : Fin n // i ∉ L}))ᶜ := by
            change u ∉ (↑((univ \ X) \ Y) : Set {i : Fin n // i ∉ L})
            simp only [Finset.mem_coe, Finset.mem_sdiff]
            intro hcon
            exact absurd huX hcon.1.2
          have h2 : o u = v u := ho u huC
          rw [h2]
          change v u = (if u ∈ X then v u else z (u : Fin n))
          rw [ite_eq_left huX]
        · have huS : u ∈ univ \ X := Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huX⟩
          have h1 : z (u : Fin n) = extendObs L o (u : Fin n) :=
            hz _ (Finset.mem_coe.mpr ((Finset.mem_map' (Function.Embedding.subtype _)).mpr huS))
          have h3 : extendObs L o (u : Fin n) = o u := ids_aux_extendObs_apply L o u
          change o u = (if u ∈ X then v u else z (u : Fin n))
          rw [ite_eq_right huX, h1, h3]
    · rintro ⟨hoEq, hzS⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hzS
      simp only [Finset.mem_singleton] at hoEq
      subst hoEq
      constructor
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro w hw
        have hwN : w ∉ (↑((univ \ X) \ Y) : Set {i : Fin n // i ∉ L}) := hw
        simp only [Finset.mem_coe, Finset.mem_sdiff] at hwN
        by_cases hwX : w ∈ X
        · change (if w ∈ X then v w else z (w : Fin n)) = v w
          rw [ite_eq_left hwX]
        · have hwY : w ∈ Y := by
            by_contra hwY
            exact hwN ⟨⟨Finset.mem_univ w, hwX⟩, hwY⟩
          have hwYX : w ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hwY, hwX⟩
          have h1 : z (w : Fin n) = extendObs L v (w : Fin n) :=
            hzS _ (Finset.mem_coe.mpr ((Finset.mem_map' (Function.Embedding.subtype _)).mpr hwYX))
          change (if w ∈ X then v w else z (w : Fin n)) = v w
          rw [ite_eq_right hwX, h1, ids_aux_extendObs_apply L v w]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro i hi
        simp only [Finset.mem_coe, Finset.mem_map, Function.Embedding.subtype_apply] at hi
        obtain ⟨u, hu, rfl⟩ := hi
        have huX : u ∉ X := (Finset.mem_sdiff.mp hu).2
        rw [ids_aux_extendObs_apply]
        change z (u : Fin n) = (if u ∈ X then v u else z (u : Fin n))
        rw [ite_eq_right huX]
  have hsub : univ.filter (fun z : Fin n → α =>
        ∀ i ∈ (↑(Y.map (Function.Embedding.subtype _)) : Set (Fin n)),
        z i = extendObs L v i) ⊆
      univ.filter (fun z : Fin n → α =>
        ∀ i ∈ (↑((Y \ X).map (Function.Embedding.subtype _)) : Set (Fin n)),
        z i = extendObs L v i) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    intro i hi
    simp only [Finset.mem_coe, Finset.mem_map, Function.Embedding.subtype_apply] at hi
    obtain ⟨w, hw, rfl⟩ := hi
    have hwY : w ∈ Y := (Finset.mem_sdiff.mp hw).1
    exact hz _ (Finset.mem_coe.mpr ((Finset.mem_map' (Function.Embedding.subtype _)).mpr hwY))
  have hvan : ∀ z ∈ univ.filter (fun z : Fin n → α =>
        ∀ i ∈ (↑((Y \ X).map (Function.Embedding.subtype _)) : Set (Fin n)),
        z i = extendObs L v i),
      z ∉ univ.filter (fun z : Fin n → α =>
        ∀ i ∈ (↑(Y.map (Function.Embedding.subtype _)) : Set (Fin n)),
        z i = extendObs L v i) →
      (b.mutilateSet (X.map (Function.Embedding.subtype _))
        (extendObs L (fun u : {i : Fin n // i ∉ L} =>
          if u ∈ X then v u else z (u : Fin n)))).joint z = 0 := by
    intro z hzS hznL
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hzS hznL
    rw [not_forall] at hznL
    obtain ⟨i, hi⟩ := hznL
    rw [not_imp] at hi
    obtain ⟨hiY, hne⟩ := hi
    simp only [Finset.mem_coe, Finset.mem_map, Function.Embedding.subtype_apply] at hiY
    obtain ⟨w, hwY, rfl⟩ := hiY
    have hwX : w ∈ X := by
      by_contra hwX
      have hwYX : w ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hwY, hwX⟩
      have hmem : (w : Fin n) ∈ (Y \ X).map (Function.Embedding.subtype _) :=
        (Finset.mem_map' (Function.Embedding.subtype _)).mpr hwYX
      exact hne (hzS _ (Finset.mem_coe.mpr hmem))
    have hwXhat : (w : Fin n) ∈ X.map (Function.Embedding.subtype _) :=
      (Finset.mem_map' (Function.Embedding.subtype _)).mpr hwX
    have hval : extendObs L (fun u : {i : Fin n // i ∉ L} =>
        if u ∈ X then v u else z (u : Fin n)) (w : Fin n) = extendObs L v (w : Fin n) := by
      simp only [ids_aux_extendObs_apply]
      rw [ite_eq_left hwX]
    have hnc : z (w : Fin n) ≠ extendObs L (fun u : {i : Fin n // i ∉ L} =>
        if u ∈ X then v u else z (u : Fin n)) (w : Fin n) := by
      rw [hval]
      exact hne
    rw [BayesNet.joint_mutilateSet]
    refine Finset.prod_eq_zero (Finset.mem_univ (w : Fin n)) ?_
    rw [ite_eq_left hwXhat, ite_eq_right hnc]
  have hsumm : ∀ z : Fin n → α,
      (b.mutilateSet (X.map (Function.Embedding.subtype _)) (extendObs L v)).joint z =
        (b.mutilateSet (X.map (Function.Embedding.subtype _))
          (extendObs L (fun u : {i : Fin n // i ∉ L} =>
            if u ∈ X then v u else z (u : Fin n)))).joint z := by
    intro z
    simp only [BayesNet.joint_mutilateSet]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : j ∈ X.map (Function.Embedding.subtype _)
    · rw [ite_eq_left hj, ite_eq_left hj]
      have hval : extendObs L (fun u : {i : Fin n // i ∉ L} =>
        if u ∈ X then v u else z (u : Fin n)) j = extendObs L v j := by
        rw [Finset.mem_map] at hj
        obtain ⟨u, huX, heq⟩ := hj
        have heq' : (u : Fin n) = j := heq
        subst heq'
        simp only [ids_aux_extendObs_apply]
        change (if u ∈ X then v u else z (u : Fin n)) = v u
        rw [ite_eq_left huX]
      by_cases hc : z j = extendObs L v j
      · have hcL : z j = extendObs L (fun u : {i : Fin n // i ∉ L} =>
        if u ∈ X then v u else z (u : Fin n)) j := by
          rw [hval]
          exact hc
        rw [ite_eq_left hcL, ite_eq_left hc]
      · have hcL : ¬ z j = extendObs L (fun u : {i : Fin n // i ∉ L} =>
        if u ∈ X then v u else z (u : Fin n)) j := by
          rw [hval]
          exact hc
        rw [ite_eq_right hcL, ite_eq_right hc]
    · rw [ite_eq_right hj, ite_eq_right hj]
  rw [Finset.sum_comm' (t' := univ.filter (fun z : Fin n → α =>
      ∀ i ∈ (↑((Y \ X).map (Function.Embedding.subtype _)) : Set (Fin n)),
      z i = extendObs L v i))
    (s' := fun z : Fin n → α =>
      ({(fun u : {i : Fin n // i ∉ L} => if u ∈ X then v u else z (u : Fin n))} :
        Finset ({i : Fin n // i ∉ L} → α))) hcorr]
  simp only [Finset.sum_singleton]
  rw [← Finset.sum_subset hsub hvan]
  exact Finset.sum_congr rfl (fun z _ => hsumm z)

/-- **Soundness of the ID algorithm.** Let a Bayesian network whose nodes take values in a finite
nonempty type have latent node set `L`, let `σ` be a topological order of its latent projection
onto the observed nodes, and suppose the observed law is strictly positive at every observed
assignment. Let `X` and `Y` be disjoint sets of observed nodes. If the ID algorithm (Shpitser and
Pearl, AAAI 2006, Fig. 3), run on the latent projection with the order `σ`, returns an expression
`e` for the effect of `do(X)` on `Y`, then `e`, evaluated against the observed law, equals the
effect `P_x(y)` at every observed assignment `v`, with `x` and `y` the values of `v` on `X` and
`Y`. No semi-Markovian hypothesis is needed. When ID returns a failure pair `(F, F')` instead,
nothing is claimed: neither that `(F, F')` is a hedge nor that `P_x(y)` is not identified.

Source: I. Shpitser and J. Pearl, *Identification of Joint Interventional Distributions in
Recursive Semi-Markovian Causal Models*, AAAI 2006 (technical report R-327), Theorem 5.
<https://ftp.cs.ucla.edu/pub/stat_ser/r327.pdf>

Source: I. Shpitser and J. Pearl, *Identification of Conditional Interventional Distributions*,
UAI 2006 (technical report R-329), Section 4, where the result is restated.
<https://ftp.cs.ucla.edu/pub/stat_ser/r329-uai.pdf> -/
theorem ID_sound
    {σ : {i : Fin n // i ∉ L} ≃ Fin (Fintype.card {i : Fin n // i ∉ L})}
    (hσ : ∀ ⦃u w⦄, (b.latentProjection L).dir u w → σ u < σ w)
    (hpos : ∀ v, 0 < b.observedLaw L v)
    {Y X : Finset {i : Fin n // i ∉ L}} (hXY : Disjoint X Y) {e : IdExpr {i : Fin n // i ∉ L}}
    (h : (b.latentProjection L).ID σ Y X = .ok e) (v : {i : Fin n // i ∉ L} → α) :
    e.eval (b.observedLaw L) v = b.doMarginal L X Y v := by
  have : DecidableEq α := fun a b => Classical.propDecidable (a = b)
  have hP : ∀ w : {i : Fin n // i ∉ L} → α,
      IdExpr.obs.eval (b.observedLaw L) w = b.qFactor L Finset.univ w :=
    fun w => (congrFun (qFactor_univ b L) w).symm
  have hrec : (b.latentProjection L).idRec σ Y X Finset.univ IdExpr.obs = .ok e := h
  have h1 := idRec_sound b L hσ hpos hP (Finset.subset_univ X) (Finset.subset_univ Y)
    hXY hrec v
  have h2 := doMarginal_eq_marginal_qFactor b L X Y v
  exact h1.trans h2.symm

/-- **Soundness of the ID algorithm for a fixed causal diagram.** Let `G` be an acyclic directed
mixed graph on the observed nodes of a latent set `L`, with a topological order `σ`, and let `X`
and `Y` be disjoint sets of observed nodes. If the ID algorithm, run on `G` with the order `σ`,
returns an expression `e` for the effect of `do(X)` on `Y`, then for every Bayesian network of
`tianClass L G` (node values in one finite nonempty type, no latent node a descendant of an
observed node, latent projection `G`, observed law strictly positive at every observed
assignment), `e` evaluated against that network's observed law equals its effect `P_x(y)` at
every observed assignment. The descendant condition is Tian and Pearl's 2002 semi-Markovian
hypothesis (AAAI-02, p. 568), which `ID_sound` shows is not needed. Nothing is claimed when ID
returns a failure pair. -/
theorem ID_sound_of_mem_tianClass {G : ADMG {i : Fin n // i ∉ L}}
    {σ : {i : Fin n // i ∉ L} ≃ Fin (Fintype.card {i : Fin n // i ∉ L})}
    (hσ : ∀ ⦃u w⦄, G.dir u w → σ u < σ w)
    {Y X : Finset {i : Fin n // i ∉ L}} (hXY : Disjoint X Y) {e : IdExpr {i : Fin n // i ∉ L}}
    (h : G.ID σ Y X = .ok e) {c : BayesNet α n} (hc : c ∈ tianClass L G)
    (v : {i : Fin n // i ∉ L} → α) :
    e.eval (c.observedLaw L) v = c.doMarginal L X Y v := by
  obtain ⟨-, hproj, hpos⟩ := hc
  subst hproj
  exact ID_sound c L hσ hpos hXY h v

/-- **A successful run of ID identifies the effect.** Let `G` be an acyclic directed mixed graph on
the observed nodes of a latent set `L`, with a topological order `σ`, and let `X` and `Y` be
disjoint sets of observed nodes. If the ID algorithm, run on `G` with the order `σ`, returns an
expression, then the effect `P_x(y)` is identified from the observed law on `tianClass L G`: any
two networks of that class with the same observed law have the same effect at every observed
assignment (the identifiability of Shpitser and Pearl, AAAI 2006, Definition 2). -/
theorem identifiedOn_doMarginal_of_ID_eq_ok {G : ADMG {i : Fin n // i ∉ L}}
    {σ : {i : Fin n // i ∉ L} ≃ Fin (Fintype.card {i : Fin n // i ∉ L})}
    (hσ : ∀ ⦃u w⦄, G.dir u w → σ u < σ w)
    {Y X : Finset {i : Fin n // i ∉ L}} (hXY : Disjoint X Y) {e : IdExpr {i : Fin n // i ∉ L}}
    (h : G.ID σ Y X = .ok e) :
    IdentifiedOn (tianClass (α := α) L G) (fun c : BayesNet α n => c.observedLaw L)
      (fun c => c.doMarginal L X Y) := by
  refine IdentifiedOn.of_eq_comp (fun p v => e.eval p v) ?_
  intro c hc
  show c.doMarginal L X Y = fun v => e.eval (c.observedLaw L) v
  funext v
  exact (ID_sound_of_mem_tianClass L hσ hXY h hc v).symm

end BayesNet

end Cslib.MachineLearning.GraphicalModels
