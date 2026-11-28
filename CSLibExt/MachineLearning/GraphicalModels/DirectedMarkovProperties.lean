/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.MarkovFactorization
import Mathlib.Tactic.TFAE

/-!
# The directed Markov properties are equivalent

For a directed acyclic graph (the graph of a Bayesian network `b`, nodes in a topological
order; its tables play no role) and any law `P` on `Fin n → α` with `α` finite, the following
are equivalent (Lauritzen, *Markov properties for directed graphs*, 2009: `(G) ⇔ (L) ⇔ (O)`, and
`(F) ⇔ (G)`):

* (F) `P` factorizes over the graph: it is the joint law of a Bayesian network on the same
  parent sets;
* (G) the global Markov property: d-separation implies conditional independence under `P`;
* (L) the local Markov property: every node is independent of its non-descendants that are not
  parents, given its parents;
* (O) the ordered Markov property (`OrderedMarkov`).

No positivity assumption is needed, in contrast with the undirected Hammersley–Clifford theorem.

`BayesNet.joint` is built through `BayesNet.toChain`, which needs a default value, so
`directedMarkov_tfae` assumes that `α` is nonempty. The section *Every finite value type* states
(F) as the factorization formula of Evans (§5.2.1), `P(x) = ∏ k, p_k(x_k | x_{pa k})` for the
tables `p_k` of a network, which is `BayesNet.joint` whenever that is defined
(`BayesNet.joint_eq_prod`), and proves the equivalences for every finite `α`. The only new case
is an empty `α`: on zero nodes it carries exactly one law, mass `1` on the empty assignment, and
exactly one network; on one node or more it carries neither a law nor a network.

## Main definitions

* `GlobalMarkovFor P b`, `LocalMarkovFor P b`: the global and local Markov properties of `P` for
  the graph of `b`.

## Main results

* `globalMarkovFor_of_factorizes`, `localMarkovFor_of_globalMarkovFor`,
  `orderedMarkov_of_localMarkovFor` and `exists_bayesNet_of_orderedMarkov`: the cycle
  `(F) ⇒ (G) ⇒ (L) ⇒ (O) ⇒ (F)`. The step (G) ⇒ (L) uses
  `BayesNet.dSeparated_localMarkov` (the parents of a node d-separate it from its other
  non-descendants), from `CSLibExt.MachineLearning.GraphicalModels.MarkovBlanket`.
* `directedMarkov_tfae`: the four properties are equivalent.
* `orderedMarkov_iff_exists_bayesNet_prod`, `localMarkovFor_of_orderedMarkov` and
  `directedMarkov_tfae_prod`: for every finite `α`, empty or not, with (F) in product form,
  (O) ⇔ (F), Evans's (5.1) ⇒ (5.2), that is (O) ⇒ (L), and the equivalence of the four
  properties.

## References

* S. L. Lauritzen, *Markov properties for directed graphs*, Graphical Models lecture notes,
  University of Oxford (2009).
* J. Pearl, *Causal diagrams for empirical research*, Biometrika 82(4) (1995), 669–710, §2.1.
* R. Evans, *Causal Inference*, APTS lecture notes, Chapter 5, *Graphical Models*, §5.2.1
  (the factorization property and equations (5.1) and (5.2)),
  https://www.stats.ox.ac.uk/~evans/APTS/gm.html.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity MetaMathlibExt.FiniteWeight

variable {α : Type*} {n : ℕ}

/-- **The global Markov property for a graph** (Lauritzen 2009, property (G)): every
d-separation in the graph of `b` is a conditional independence of `P`. Like `CondIndep`, it is
defined for an arbitrary weight function `P`; it is the property of a law when `P` is
nonnegative with total mass `1`, as in `directedMarkov_tfae`. For the zero weight it holds for
every graph. -/
def GlobalMarkovFor [Fintype α] (P : (Fin n → α) → ℝ) (b : BayesNet α n) : Prop :=
  ∀ X Y Z : Set (Fin n), b.DSeparated X Y Z → CondIndep P X Y Z

/-- **The local Markov property for a graph** (Lauritzen 2009, property (L)): under `P`, every
node is conditionally independent of its non-descendants that are not its parents, given its
parents, in the graph of `b`. Like `CondIndep`, it is defined for an arbitrary weight function
`P`; it is the property of a law when `P` is nonnegative with total mass `1`, as in
`directedMarkov_tfae`. For the zero weight it holds for every graph. -/
def LocalMarkovFor [Fintype α] (P : (Fin n → α) → ℝ) (b : BayesNet α n) : Prop :=
  ∀ k, CondIndep P {k} {j | ¬b.IsDescendant k j ∧ ¬b.Edge j k} {j | b.Edge j k}

/-- **Factorization implies the global Markov property** ((F) ⇒ (G)). The joint law of a network
on the parent sets of `b` has the global Markov property for the graph of `b`. -/
theorem globalMarkovFor_of_factorizes [Fintype α] [Nonempty α] {b b' : BayesNet α n}
    (h : b'.pa = b.pa) : GlobalMarkovFor b'.joint b := by
  intro X Y Z hd
  apply b'.condIndep_of_dSeparated
  obtain ⟨pa, cpt⟩ := b
  obtain ⟨pa', cpt'⟩ := b'
  simp only at h
  subst h
  exact hd

/-- **The global Markov property implies the local one** ((G) ⇒ (L)). -/
theorem localMarkovFor_of_globalMarkovFor [Fintype α] {P : (Fin n → α) → ℝ} {b : BayesNet α n}
    (h : GlobalMarkovFor P b) : LocalMarkovFor P b :=
  fun k => h _ _ _ (b.dSeparated_localMarkov k)

/-- **The local Markov property implies the ordered one** ((L) ⇒ (O)), by decomposition: the
predecessors of `k` are non-descendants of `k`. -/
theorem orderedMarkov_of_localMarkovFor [Fintype α] {P : (Fin n → α) → ℝ} {b : BayesNet α n}
    (h : LocalMarkovFor P b) : OrderedMarkov P b.pa := by
  classical
  intro k
  have hl := h k
  set B := univ.filter fun j => ¬b.IsDescendant k j ∧ ¬b.Edge j k
  have eK : ({k} : Set (Fin n)) = ↑({k} : Finset (Fin n)) := by simp
  have eB : {j | ¬b.IsDescendant k j ∧ ¬b.Edge j k} = (↑B : Set (Fin n)) := by ext j; simp [B]
  have ePa : {j | b.Edge j k} = (↑(parentSet b.pa k) : Set (Fin n)) := by
    ext j
    simp only [Set.mem_ofPred_eq, mem_coe, mem_parentSet]
    rfl
  rw [eK, eB, ePa] at hl
  have hsub : nonParentPred b.pa k ⊆ B := by
    intro j hj
    simp only [nonParentPred, mem_filter, mem_univ, true_and] at hj
    simp only [B, mem_filter, mem_univ, true_and]
    exact ⟨fun hd => absurd hd.le (not_le.2 hj.1), fun he => hj.2 (mem_parentSet.2 he)⟩
  have hdisj : Disjoint B {k} := by
    rw [disjoint_singleton_right]
    intro hk
    simp only [B, mem_filter, mem_univ, true_and] at hk
    exact hk.1 .refl
  exact condIndep_symm (condIndep_mono_left (condIndep_symm hl) hsub hdisj)

/-- **The directed Markov properties are equivalent** (Lauritzen 2009): for a law `P` on
`Fin n → α` and the graph of a Bayesian network `b`, factorization over the graph, the global,
the local and the ordered Markov properties are equivalent. -/
theorem directedMarkov_tfae [Fintype α] [Nonempty α] (P : (Fin n → α) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (h1 : ∑ x, P x = 1) (b : BayesNet α n) :
    [∃ b' : BayesNet α n, b'.pa = b.pa ∧ b'.joint = P, GlobalMarkovFor P b, LocalMarkovFor P b,
      OrderedMarkov P b.pa].TFAE := by
  tfae_have 1 → 2 := by
    rintro ⟨b', hpa, rfl⟩
    exact globalMarkovFor_of_factorizes hpa
  tfae_have 2 → 3 := localMarkovFor_of_globalMarkovFor
  tfae_have 3 → 4 := orderedMarkov_of_localMarkovFor
  tfae_have 4 → 1 := exists_bayesNet_of_orderedMarkov P hP h1 b.pa
  tfae_finish

/-! ### Every finite value type

The results above assume `[Nonempty α]` because they go through `BayesNet.joint`. Here (F) is the
factorization formula of Evans (§5.2.1) for the tables of a network,
`x ↦ ∏ k : Fin n, (b.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k)`, the right-hand side
of `BayesNet.joint_eq_prod`, and `α` is any finite type, empty or not. For nonempty `α` the
product is `BayesNet.joint`, and these are the results above in product form. For empty `α` there
is no network on one node or more (`BayesNet.instIsEmptySucc`) and exactly one on zero nodes
(`BayesNet.instUniqueZero`), and the only law on zero nodes is mass `1` on the empty
assignment. -/

section EveryFiniteValueType

/-- **A network with a node has a nonempty value type.** Let $\alpha$ be a type and $n$ a
natural number. If $b$ is a Bayesian network with values in $\alpha$ on the $n + 1$ nodes
$0, \dots, n$, then $\alpha$ is nonempty: the table of node $0$, which has no parents, is a
probability distribution on $\alpha$. -/
theorem BayesNet.nonempty_of_succ (b : BayesNet α (n + 1)) : Nonempty α := by
  exact StdSimplex.nonempty (b.cpt ⟨0, Nat.zero_lt_succ n⟩ fun j => j.1.elim0)

/-- **No network with a node over an empty value type.** Let $\alpha$ be an empty type. For
every natural number $n$ there is no Bayesian network with values in $\alpha$ on the $n + 1$
nodes $0, \dots, n$. -/
instance BayesNet.instIsEmptySucc [IsEmpty α] : IsEmpty (BayesNet α (n + 1)) := by
  refine ⟨fun b => ?_⟩
  obtain ⟨a⟩ := BayesNet.nonempty_of_succ b
  exact isEmptyElim a

/-- **The network on zero nodes.** For every type $\alpha$, empty or not, there is exactly one
Bayesian network with values in $\alpha$ on zero nodes; it has no parent sets and no tables. -/
instance BayesNet.instUniqueZero : Unique (BayesNet α 0) where
  default := { pa := fun k => k.elim0, cpt := fun k => k.elim0 }
  uniq := by
    intro b
    obtain ⟨pa, cpt⟩ := b
    have hpa : pa = (fun k => k.elim0) := funext fun k => k.elim0
    subst hpa
    have hcpt : cpt = (fun k => k.elim0) := funext fun k => k.elim0
    rw [hcpt]

/-- On zero nodes every conditional independence statement holds, for every weight. -/
private theorem condIndep_of_fin_zero [Fintype α] (P : (Fin 0 → α) → ℝ) (X Y Z : Set (Fin 0)) :
    CondIndep P X Y Z := by
  rw [Set.eq_empty_of_isEmpty X, Set.eq_empty_of_isEmpty Y, Set.eq_empty_of_isEmpty Z]
  intro x
  simp

/-- **The product of the tables is a law, for every finite value type.** Let $\alpha$ be a
finite type, empty or not, and let $b$ be a Bayesian network with values in $\alpha$ on the
nodes $0, \dots, n - 1$, with table $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ at node $k$. Then
$$\sum_{x \in \alpha^n} \prod_{k < n} p_k(x_k \mid x_{\mathrm{pa}(k)}) = 1.$$
For nonempty $\alpha$ the product is the joint law `BayesNet.joint` (`BayesNet.joint_eq_prod`)
and this is `BayesNet.sum_joint`; for empty $\alpha$ the network has zero nodes and the sum has a
single term, the empty product $1$. -/
theorem BayesNet.sum_prod_cpt [Fintype α] (b : BayesNet α n) :
    ∑ x : Fin n → α, ∏ k : Fin n, (b.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k) = 1 := by
  rcases isEmpty_or_nonempty α with hempty | hne
  · cases n with
    | zero =>
      rw [Fintype.sum_unique]
      simp
    | succ n => exact isEmptyElim b
  · have hfun : (fun x => ∏ k : Fin n, (b.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k)) =
        b.joint := by
      funext x
      exact (BayesNet.joint_eq_prod b x).symm
    rw [hfun]
    exact BayesNet.sum_joint b

/-- **Factorization implies the ordered Markov property, for every finite value type**
((F) ⇒ (O)). Let $\alpha$ be a finite type, empty or not, and let $b$ be a Bayesian network with
values in $\alpha$ on the nodes $0, \dots, n - 1$, with table $p_k(\cdot \mid x_{\mathrm{pa}(k)})$
at node $k$. Then the product of the tables,
$P(x) = \prod_{k < n} p_k(x_k \mid x_{\mathrm{pa}(k)})$, has the ordered Markov property for the
parent sets of $b$: under $P$, every node is conditionally independent of the earlier nodes that
are not its parents, given its parents (Evans, (5.1), for the order $0, \dots, n - 1$). -/
theorem orderedMarkov_prod_cpt [Fintype α] (b : BayesNet α n) :
    OrderedMarkov
      (fun x => ∏ k : Fin n, (b.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k)) b.pa := by
  rcases isEmpty_or_nonempty α with hempty | hne
  · cases n with
    | zero => exact fun k => k.elim0
    | succ n => exact isEmptyElim b
  · have hfun : (fun x => ∏ k : Fin n, (b.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k)) =
        b.joint := by
      funext x
      exact (BayesNet.joint_eq_prod b x).symm
    rw [hfun]
    exact orderedMarkov_joint b

/-- **Markov laws factorize, for every finite value type** ((O) ⇒ (F)). Let $\alpha$ be a finite
type, empty or not, let $P$ be a law on $\alpha^n$, that is $P(x) \ge 0$ for every $x$ and
$\sum_x P(x) = 1$, and give each node $k$ a set `pa k` of parents among $0, \dots, k - 1$. If
$P$ has the ordered Markov property for these parent sets, then there is a Bayesian network $b$
on them whose tables $p_k$ multiply to $P$:
$P(x) = \prod_{k < n} p_k(x_k \mid x_{\mathrm{pa}(k)})$ for every $x \in \alpha^n$. The network
need not be unique: a table row at parent values of probability zero is arbitrary. -/
theorem exists_bayesNet_prod_of_orderedMarkov [Fintype α] (P : (Fin n → α) → ℝ)
    (hP : ∀ x, 0 ≤ P x) (h1 : ∑ x, P x = 1) (pa : (k : Fin n) → Finset (Fin k))
    (hO : OrderedMarkov P pa) :
    ∃ b : BayesNet α n, b.pa = pa ∧
      ∀ x, P x = ∏ k : Fin n, (b.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k) := by
  rcases isEmpty_or_nonempty α with hempty | hne
  · cases n with
    | zero =>
      refine ⟨default, funext fun k => k.elim0, ?_⟩
      intro x
      have hx : x = default := Subsingleton.elim _ _
      have hsum : ∑ y : Fin 0 → α, P y = P default := Fintype.sum_unique P
      have hPx : P x = 1 := by rw [hx, ← hsum, h1]
      rw [hPx]
      simp
    | succ n =>
      simp at h1
  · obtain ⟨b, hbpa, hbjoint⟩ := exists_bayesNet_of_orderedMarkov P hP h1 pa hO
    refine ⟨b, hbpa, fun x => ?_⟩
    rw [← hbjoint]
    exact BayesNet.joint_eq_prod b x

/-- **The ordered Markov property is equivalent to factorization, for every finite value type**
(Evans, §5.2.1: the factorization property and (5.1)). Let $\alpha$ be a finite type, empty or
not, let $P$ be a law on $\alpha^n$ ($P(x) \ge 0$ for every $x$ and $\sum_x P(x) = 1$), and give
each node $k$ a set `pa k` of parents among $0, \dots, k - 1$. Then $P$ has the ordered Markov
property for these parent sets if and only if there is a Bayesian network on them whose tables
$p_k$ satisfy $P(x) = \prod_{k < n} p_k(x_k \mid x_{\mathrm{pa}(k)})$ for every $x \in \alpha^n$.
This is `orderedMarkov_iff_exists_bayesNet` without the assumption that $\alpha$ is nonempty. -/
theorem orderedMarkov_iff_exists_bayesNet_prod [Fintype α] (P : (Fin n → α) → ℝ)
    (hP : ∀ x, 0 ≤ P x) (h1 : ∑ x, P x = 1) (pa : (k : Fin n) → Finset (Fin k)) :
    OrderedMarkov P pa ↔ ∃ b : BayesNet α n, b.pa = pa ∧
      ∀ x, P x = ∏ k : Fin n, (b.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k) := by
  constructor
  · exact exists_bayesNet_prod_of_orderedMarkov P hP h1 pa
  · rintro ⟨b, hbpa, hprod⟩
    have hfun : P =
        (fun x => ∏ k : Fin n, (b.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k)) :=
      funext hprod
    rw [hfun, ← hbpa]
    exact orderedMarkov_prod_cpt b

/-- **Factorization implies the local Markov property, for every finite value type**
((F) ⇒ (L)). Let $\alpha$ be a finite type, empty or not, and let $b$ and $b'$ be Bayesian
networks with values in $\alpha$ on the nodes $0, \dots, n - 1$ with the same parent sets. Then
the product of the tables $p'_k$ of $b'$,
$P(x) = \prod_{k < n} p'_k(x_k \mid x_{\mathrm{pa}(k)})$, has the local Markov property for the
graph of $b$: under $P$, every node is conditionally independent of its non-descendants that are
not its parents, given its parents (Evans, (5.2)). -/
theorem localMarkovFor_prod_cpt [Fintype α] {b b' : BayesNet α n} (h : b'.pa = b.pa) :
    LocalMarkovFor
      (fun x => ∏ k : Fin n, (b'.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k)) b := by
  rcases isEmpty_or_nonempty α with hempty | hne
  · cases n with
    | zero => exact fun k => k.elim0
    | succ n => exact isEmptyElim b'
  · have hfun : (fun x => ∏ k : Fin n, (b'.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k)) =
        b'.joint := by
      funext x
      exact (BayesNet.joint_eq_prod b' x).symm
    rw [hfun]
    exact localMarkovFor_of_globalMarkovFor (globalMarkovFor_of_factorizes h)

/-- **The ordered Markov property implies the local one, for every finite value type**
(Evans, §5.2.1: (5.1) implies (5.2)). Let $\alpha$ be a finite type, empty or not, let $P$ be a
law on $\alpha^n$ ($P(x) \ge 0$ for every $x$ and $\sum_x P(x) = 1$), and let $b$ be a Bayesian
network on the nodes $0, \dots, n - 1$, whose tables play no role. If $P$ has the ordered Markov
property for the parent sets of $b$, in the order $0, \dots, n - 1$, then it has the local Markov
property for the graph of $b$: every node is conditionally independent of its non-descendants
that are not its parents, given its parents. Evans obtains (5.2) from (5.1) by choosing a
topological order for each node; here the single order $0, \dots, n - 1$ suffices. -/
theorem localMarkovFor_of_orderedMarkov [Fintype α] (P : (Fin n → α) → ℝ)
    (hP : ∀ x, 0 ≤ P x) (h1 : ∑ x, P x = 1) (b : BayesNet α n)
    (hO : OrderedMarkov P b.pa) : LocalMarkovFor P b := by
  rcases isEmpty_or_nonempty α with hempty | hne
  · cases n with
    | zero => exact fun k => k.elim0
    | succ n => exact isEmptyElim b
  · obtain ⟨b', hbpa, hbjoint⟩ := exists_bayesNet_of_orderedMarkov P hP h1 b.pa hO
    rw [← hbjoint]
    exact localMarkovFor_of_globalMarkovFor (globalMarkovFor_of_factorizes hbpa)

/-- **The directed Markov properties are equivalent, for every finite value type.** Let
$\alpha$ be a finite type, empty or not, let $P$ be a law on $\alpha^n$ ($P(x) \ge 0$ for every
$x$ and $\sum_x P(x) = 1$), and let $b$ be a Bayesian network on the nodes $0, \dots, n - 1$,
whose tables play no role. The following are equivalent: (F) there is a Bayesian network on the
parent sets of $b$ whose tables $p_k$ satisfy
$P(x) = \prod_{k < n} p_k(x_k \mid x_{\mathrm{pa}(k)})$ for every $x$; (G) $P$ has the global
Markov property for the graph of $b$; (L) $P$ has the local Markov property for it; (O) $P$ has
the ordered Markov property for the parent sets of $b$. This is `directedMarkov_tfae` without
the assumption that $\alpha$ is nonempty, with (F) in product form. -/
theorem directedMarkov_tfae_prod [Fintype α] (P : (Fin n → α) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (h1 : ∑ x, P x = 1) (b : BayesNet α n) :
    [∃ b' : BayesNet α n, b'.pa = b.pa ∧
        ∀ x, P x = ∏ k : Fin n, (b'.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k),
      GlobalMarkovFor P b, LocalMarkovFor P b, OrderedMarkov P b.pa].TFAE := by
  rcases isEmpty_or_nonempty α with hempty | hne
  · cases n with
    | zero =>
      have hO : OrderedMarkov P b.pa := fun k => k.elim0
      have h1st : ∃ b' : BayesNet α 0, b'.pa = b.pa ∧
          ∀ x, P x = ∏ k : Fin 0, (b'.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k) :=
        exists_bayesNet_prod_of_orderedMarkov P hP h1 b.pa hO
      have hG : GlobalMarkovFor P b := fun X Y Z _ => condIndep_of_fin_zero P X Y Z
      have hL : LocalMarkovFor P b := fun k => k.elim0
      refine List.tfae_of_forall fun a ha => iff_true_intro ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact h1st
      · exact hG
      · exact hL
      · exact hO
    | succ n =>
      simp at h1
  · have h1equiv : (∃ b' : BayesNet α n, b'.pa = b.pa ∧ b'.joint = P) ↔
        (∃ b' : BayesNet α n, b'.pa = b.pa ∧
          ∀ x, P x = ∏ k : Fin n, (b'.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k)) := by
      constructor
      · rintro ⟨b', hbpa, hbjoint⟩
        refine ⟨b', hbpa, fun x => ?_⟩
        rw [← hbjoint]
        exact BayesNet.joint_eq_prod b' x
      · rintro ⟨b', hbpa, hprod⟩
        refine ⟨b', hbpa, ?_⟩
        funext x
        rw [BayesNet.joint_eq_prod b' x]
        exact (hprod x).symm
    have htfae := directedMarkov_tfae P hP h1 b
    rw [h1equiv] at htfae
    exact htfae

end EveryFiniteValueType

end Cslib.MachineLearning.GraphicalModels
