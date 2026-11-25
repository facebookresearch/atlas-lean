/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CausalAdjustment
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Structural causal models, interventions and counterfactuals

A *Markovian structural causal model* (Pearl 1995, eq. (3); Pearl, *Statistics Surveys*
2009, §3.2 and Theorem 1) on endogenous variables `X 0, …, X (n - 1)`, listed in a topological
order, assigns to each node `k` a set of parents among the earlier nodes, an exogenous disturbance
`U k` with law `noise k` on a finite type `β`, the disturbances being mutually independent, and
a mechanism (structural equation) `X k = mech k (X_{pa k}) (U k)`. Every value `u` of the
disturbances determines the values of all endogenous variables (`SCM.solve`); the law of the
model (`SCM.law`) is the image of the product law of the disturbances.

The intervention `do(X_W = w)` replaces the equations of the nodes in `W` by the constants
`X j = w j` and keeps all other equations (`SCM.doSet`: the submodel `M_x` of Pearl 1995,
Definition 2, and of Pearl, *Statistics Surveys* 2009, eq. (7)). The unit-level counterfactual
`Y_x(u)` is the solution of that submodel at `u` (`SCM.counterfactual`: Pearl, *Statistics
Surveys* 2009, Definition 4, eq. (27)).

## Main definitions

* `SCM α β n`: a Markovian structural causal model; `SCM.solve s u`: its unique solution at the
  disturbance value `u`; `SCM.law s`: the law of the endogenous variables.
* `SCM.toBayesNet s`: its causal Bayesian network, whose table at node `k` is the law of
  `mech k z (U k)`.
* `SCM.doSet s W w`: the submodel of the intervention `do(X_W = w)`.
* `SCM.counterfactual s W w u`: the counterfactual values `X_{W ← w}(u)`.
* `SCM.cfProb s W w E hE Y`: the probability that the counterfactual event `Y` holds under
  `do(X_W = w)` given that the factual event `E` was observed, where `hE : 0 < P(E)`: as in
  Pearl's conditional probabilities, the evidence must have positive probability.

## Main results

* `SCM.solve_eq_iff`: the solution is the unique assignment satisfying every structural
  equation.
* `SCM.law_eq_joint`: **the causal Markov condition** (Pearl, *Statistics Surveys* 2009,
  Theorem 1, eq. (15)): the law of a Markovian model factorizes as `∏ k P(x_k | x_{pa k})` over
  its causal diagram.
* `SCM.law_doSet`: **interventions are truncated factorizations** (Pearl, *Statistics Surveys*
  2009, Corollary 1, eq. (17); Pearl 1995, eq. (5)): the law of the submodel of `do(X_W = w)` is
  the joint of the mutilated network `BayesNet.mutilateSet`; `SCM.law_doSet_singleton`: for one
  node it is the joint of `BayesNet.intervene`, so the back-door and front-door formulas of
  `CSLibExt/MachineLearning/GraphicalModels/CausalAdjustment.lean` identify the causal effects
  of the model.
* `SCM.counterfactual_of_mem` (effectiveness) and `SCM.counterfactual_eq_solve` (consistency,
  Pearl, *Statistics Surveys* 2009, eq. (36): if `X_W(u) = w` then `X_{W ← w}(u) = X(u)`).
* `SCM.cfProb_true`: without evidence, the counterfactual probability is the interventional
  probability `P(Y | do(X_W = w))`; `SCM.cfProb_of_consistent`: when the evidence forces
  `X_W = w`, it is the observational conditional probability `P(Y | E)`.
* `SCM.cfProb_necessity`, `SCM.cfProb_necessity_eq`: **the probability of necessity under
  monotonicity** (Pearl, *Statistics Surveys* 2009, Theorem 3, eq. (54)):
  `PN = (P(y) - P(y | do(x'))) / P(x, y)`.

## Relation to `CSLibExt.MachineLearning.GraphicalModels.StructuralCausalModels`

That module models the same objects as `FiniteSCM α n U`, in this namespace, with a noise type per
node and the noise laws passed separately, and proves the causal Markov condition and truncated
factorization (`FiniteSCM.inducedLaw_eq_joint`, `FiniteSCM.inducedLaw_doSet`). Its counterfactuals
intervene on one node; it adds potential-outcome results and has no `cfProb_necessity` analogue.

## References

* J. Pearl, *Causal diagrams for empirical research*, Biometrika 82(4) (1995), 669–710, §2.2.
* J. Pearl, *Causal inference in statistics: An overview*, Statistics Surveys 3 (2009),
  96–146, §3.1–3.2, §3.4 and §4.1.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity

variable {α β : Type*}

/-- **Weights of an image law.** The weight of `a` under the image of a finite law `w` by `g`
is the total weight of the preimage of `a`. -/
theorem stdSimplex_map_weights [Fintype β] [DecidableEq α] (w : StdSimplex ℝ β) (g : β → α)
    (a : α) : (w.map g).weights a = ∑ e, w.weights e * if g e = a then 1 else 0 := by
  rw [StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_apply,
    Finsupp.sum_fintype _ _ (fun _ => by simp)]
  refine sum_congr rfl fun e _ => ?_
  rw [Finsupp.single_apply]
  split_ifs <;> simp

/-- **Markovian structural causal model** (Pearl 1995, eq. (3); Pearl, *Statistics Surveys*
2009, §3.2): endogenous variables on nodes `0, …, n - 1` in a topological order, each node `k`
with parents among the earlier nodes, a disturbance `U k` with law `noise k` (the disturbances
are mutually independent), and a structural equation `X k = mech k (X_{pa k}) (U k)`. -/
structure SCM (α β : Type*) (n : ℕ) where
  /-- The parents of node `k`, among the nodes `0, …, k - 1`. -/
  pa : (k : Fin n) → Finset (Fin k)
  /-- The law of the disturbance `U k` of node `k`. -/
  noise : Fin n → StdSimplex ℝ β
  /-- The structural equation of node `k`: its value given the values of its parents and of its
  disturbance. -/
  mech : (k : Fin n) → (pa k → α) → β → α

namespace SCM

variable {n : ℕ} (s : SCM α β n)

/-- **Parent values in a structural causal model.** The values of the parents of node `k` in a
full assignment `x`. -/
def paVal (k : Fin n) (x : Fin n → α) : s.pa k → α :=
  fun j => x (Fin.castLE k.2.le j)

/-- **Solution of the structural equations.** The values of the endogenous variables at the
disturbance value `u`, computed node by node along the topological order. -/
def solve (u : Fin n → β) (k : Fin n) : α :=
  s.mech k (fun j => solve u (Fin.castLE k.2.le j)) (u k)
termination_by k.val
decreasing_by simp only [Fin.val_castLE]; exact j.1.2

/-- **The solution satisfies the structural equations.** The solution satisfies the structural
equation of every node. -/
theorem solve_eq (u : Fin n → β) (k : Fin n) :
    s.solve u k = s.mech k (s.paVal k (s.solve u)) (u k) := by
  rw [solve]
  rfl

/-- **Uniqueness of the solution**: an assignment is the solution at `u` if and only if it
satisfies every structural equation at `u`. -/
theorem solve_eq_iff (u : Fin n → β) (x : Fin n → α) :
    s.solve u = x ↔ ∀ k, s.mech k (s.paVal k x) (u k) = x k := by
  constructor
  · rintro rfl k
    exact (s.solve_eq u k).symm
  · intro h
    have key : ∀ m (k : Fin n), k.val = m → s.solve u k = x k := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro k hk
        rw [s.solve_eq, ← h k]
        congr 1
        funext j
        exact ih _ (by simp only [Fin.val_castLE]; omega) _ rfl
    exact funext fun k => key _ k rfl

/-- **Law of a structural causal model.** The law of the endogenous variables: the image of the
product law of the disturbances by the solution map. -/
noncomputable def law [Fintype β] [DecidableEq α] (x : Fin n → α) : ℝ :=
  ∑ u : Fin n → β, (∏ k, (s.noise k).weights (u k)) * if s.solve u = x then 1 else 0

/-- **The causal Bayesian network of a structural causal model**: same parents, and at node `k`
the table `z ↦ law of mech k z (U k)`. -/
noncomputable def toBayesNet : BayesNet α n where
  pa := s.pa
  cpt k z := (s.noise k).map (s.mech k z)

/-- **The causal Markov condition** (Pearl, *Statistics Surveys* 2009, Theorem 1, eq. (15);
Pearl and Verma 1991): the law of a Markovian structural causal model factorizes over its causal
diagram: it is the joint of `s.toBayesNet`, the product over the nodes of the probability that
the node's equation produces its value from the values of its parents. -/
theorem law_eq_joint [Fintype β] [DecidableEq α] [Nonempty α] (x : Fin n → α) :
    s.law x = s.toBayesNet.joint x := by
  rw [BayesNet.joint_eq_prod]
  simp only [toBayesNet, stdSimplex_map_weights]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [prod_mul_distrib, prod_boole]
  congr 1
  simp only [mem_univ, true_implies]
  exact if_congr (s.solve_eq_iff u x) rfl rfl

/-- **The law of a structural causal model sums to one.** The law of a structural causal model
is a probability distribution. -/
theorem sum_law [Fintype β] [Fintype α] [DecidableEq α] [Nonempty α] :
    ∑ x, s.law x = 1 := by
  simp only [law_eq_joint]
  exact s.toBayesNet.sum_joint

/-! ### Interventions -/

/-- **The submodel of the intervention `do(X_W = w)`** (Pearl 1995, Definition 2; Pearl,
*Statistics Surveys* 2009, eq. (7)): the equation of every node `j ∈ W` is replaced by the
constant `X j = w j` (so `j` loses its parents), and every other equation is kept. -/
def doSet (W : Finset (Fin n)) (w : Fin n → α) : SCM α β n where
  pa j := if j ∈ W then ∅ else s.pa j
  noise := s.noise
  mech j z e := if h : j ∈ W then w j else s.mech j (fun i => z ⟨i, by simp [h]⟩) e

/-- **Network of a submodel.** The causal network of the submodel `do(X_W = w)` has the joint
of the mutilated network. -/
theorem joint_toBayesNet_doSet [Nonempty α] (W : Finset (Fin n))
    (w : Fin n → α) :
    (s.doSet W w).toBayesNet.joint = (s.toBayesNet.mutilateSet W w).joint := by
  funext x
  rw [BayesNet.joint_eq_prod, BayesNet.joint_eq_prod]
  refine prod_congr rfl fun j _ => ?_
  by_cases h : j ∈ W
  · simp only [toBayesNet, doSet, BayesNet.mutilateSet, h, dite_true]
    rw [StdSimplex.map_const]
  · simp only [toBayesNet, doSet, BayesNet.mutilateSet, h, dite_false]

/-- **Interventions are truncated factorizations** (Pearl, *Statistics Surveys* 2009,
Corollary 1, eq. (17); Pearl 1995, eq. (5)): the law of the submodel of `do(X_W = w)` is the
joint of the network of the model with the arrows into `W` removed and point masses at `w` on
`W`. -/
theorem law_doSet [Fintype β] [Nonempty α] [DecidableEq α] (W : Finset (Fin n))
    (w : Fin n → α) :
    (s.doSet W w).law = (s.toBayesNet.mutilateSet W w).joint := by
  funext x
  rw [law_eq_joint, joint_toBayesNet_doSet]

/-- **Single-node interventions in a structural causal model.** For one node, the law of the
submodel of `do(X_k = a)` is the joint of `BayesNet.intervene`; the back-door and front-door
adjustments therefore compute it from the law of the model. -/
theorem law_doSet_singleton [Fintype β] [Nonempty α] [DecidableEq α] (k : Fin n) (a : α) :
    (s.doSet {k} fun _ => a).law = (s.toBayesNet.intervene k a).joint := by
  rw [law_doSet]
  funext x
  rw [BayesNet.joint_eq_prod, BayesNet.joint_eq_prod]
  refine prod_congr rfl fun j _ => ?_
  by_cases h : j = k
  · subst h
    simp [BayesNet.mutilateSet, BayesNet.intervene]
  · simp only [BayesNet.mutilateSet, BayesNet.intervene, mem_singleton, h, dite_false]

/-! ### Counterfactuals -/

/-- **The unit-level counterfactual** (Pearl, *Statistics Surveys* 2009, Definition 4,
eq. (27)): `X_{W ← w}(u)`, the values the endogenous variables would have taken in the unit with
disturbances `u` had `X_W` been `w`, is the solution of the submodel `do(X_W = w)` at `u`. -/
def counterfactual (W : Finset (Fin n)) (w : Fin n → α) (u : Fin n → β) : Fin n → α :=
  (s.doSet W w).solve u

/-- **Effectiveness**: under `do(X_W = w)`, every node of `W` takes its forced value. -/
theorem counterfactual_of_mem {W : Finset (Fin n)} (w : Fin n → α) (u : Fin n → β) {i : Fin n}
    (hi : i ∈ W) : s.counterfactual W w u i = w i := by
  rw [counterfactual, solve_eq]
  simp [doSet, hi]

/-- **Consistency** (Pearl, *Statistics Surveys* 2009, eq. (36), `X = x ⇒ Y_x = Y`, which
§4.1 notes holds automatically under the structural definition): in a unit where `X_W` already
equals `w`, forcing `X_W = w` changes nothing: `X_{W ← w}(u) = X(u)`. -/
theorem counterfactual_eq_solve {W : Finset (Fin n)} {w : Fin n → α} {u : Fin n → β}
    (h : ∀ i ∈ W, s.solve u i = w i) : s.counterfactual W w u = s.solve u := by
  rw [counterfactual, solve_eq_iff]
  intro k
  by_cases hk : k ∈ W
  · simp only [doSet, hk, dite_true]
    exact (h k hk).symm
  · simp only [doSet, hk, dite_false]
    exact (s.solve_eq u k).symm

/-- **Counterfactual probability given evidence** (Pearl, *Statistics Surveys* 2009, §3.4,
the computation of `P(Y_{x₁} = y₁ | Y = y₀, X = x₀)` following eq. (28)): the probability that
the event `Y` holds for the counterfactual values `X_{W ← w}(u)`, under the law of the
disturbances conditioned on the event that the factual values `X(u)` satisfy `E`. The evidence
must have positive probability `P(E) = ∑_{x ∈ E} P(x) > 0`, as for every conditional probability
in the source: for impossible evidence the quotient would be `0 / 0 = 0` for every event `Y`,
the certain one included. -/
noncomputable def cfProb [Fintype β] [Fintype α] [DecidableEq α] (W : Finset (Fin n))
    (w : Fin n → α) (E : (Fin n → α) → Prop) [DecidablePred E] (_hE : 0 < ∑ x with E x, s.law x)
    (Y : (Fin n → α) → Prop) [DecidablePred Y] : ℝ :=
  (∑ u : Fin n → β, (∏ k, (s.noise k).weights (u k)) *
      ((if E (s.solve u) then 1 else 0) * if Y (s.counterfactual W w u) then 1 else 0)) /
    ∑ u : Fin n → β, (∏ k, (s.noise k).weights (u k)) * if E (s.solve u) then 1 else 0

/-- **The disturbance law sums to one.** The total mass of the product law of the
disturbances is `1`. -/
theorem sum_prod_noise [Fintype β] : ∑ u : Fin n → β, ∏ k, (s.noise k).weights (u k) = 1 := by
  rw [← Fintype.prod_sum]
  simp

/-- **Events under the law of a structural causal model.** The probability of an event under
the law of a model is the mass of the disturbances whose solution lies in it. -/
theorem sum_law_filter [Fintype β] [Fintype α] [DecidableEq α] (Y : (Fin n → α) → Prop)
    [DecidablePred Y] :
    ∑ x with Y x, s.law x =
      ∑ u : Fin n → β, (∏ k, (s.noise k).weights (u k)) * if Y (s.solve u) then 1 else 0 := by
  simp only [law]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [← mul_sum, sum_ite_eq]
  simp

/-- **Without evidence, counterfactuals are interventions**: with the certain evidence
(probability `1`), `P(Y_{W ← w} ∈ Y) = P(Y | do(X_W = w))`, the law of the submodel. -/
theorem cfProb_true [Fintype β] [Fintype α] [DecidableEq α] [Nonempty α] (W : Finset (Fin n))
    (w : Fin n → α) (Y : (Fin n → α) → Prop) [DecidablePred Y] :
    s.cfProb W w (fun _ => True) (by simp [s.sum_law]) Y =
      ∑ x with Y x, (s.doSet W w).law x := by
  rw [sum_law_filter]
  simp only [cfProb, ite_true, one_mul, mul_one]
  rw [show (∑ u : Fin n → β, ∏ k, (s.noise k).weights (u k)) = 1 from s.sum_prod_noise, div_one]
  rfl

/-- **Evidence that agrees with the antecedent**: if the evidence `E` has positive probability
and every assignment satisfying `E` has `X_W = w`, then the counterfactual probability given `E`
is the observational conditional probability `P(Y | E)` (by consistency). -/
theorem cfProb_of_consistent [Fintype β] [Fintype α] [DecidableEq α] {W : Finset (Fin n)}
    {w : Fin n → α} {E : (Fin n → α) → Prop} [DecidablePred E]
    (hEpos : 0 < ∑ x with E x, s.law x) (Y : (Fin n → α) → Prop) [DecidablePred Y]
    (hE : ∀ x, E x → ∀ i ∈ W, x i = w i) :
    s.cfProb W w E hEpos Y = (∑ x with E x ∧ Y x, s.law x) / ∑ x with E x, s.law x := by
  rw [sum_law_filter, sum_law_filter, cfProb]
  congr 1
  refine sum_congr rfl fun u _ => ?_
  by_cases hu : E (s.solve u)
  · rw [s.counterfactual_eq_solve (hE _ hu)]
    simp [hu]
  · simp [hu]

/-! ### The probability of necessity -/

/-- **Disturbances of a submodel.** The disturbances of a submodel are those of the model. -/
@[simp] theorem doSet_noise (W : Finset (Fin n)) (w : Fin n → α) :
    (s.doSet W w).noise = s.noise :=
  rfl

/-- **The probability of necessity under monotonicity** (Pearl, *Statistics Surveys* 2009,
eq. (53) and Theorem 3): in a model whose variables are all binary (the framework uses one
value type), for the treatment `X_i` and the outcome `X_j` with `P(x, y) > 0`, the probability
of necessity `PN = P(Y_{x'} = y' | X = x, Y = y)` (with `x, y` = `true` and `x', y'` = `false`)
is identified from the observational law and the interventional law of `do(X_i = false)` when
`Y` is monotonic in `X` (`Y_{x'}(u) = true` implies `Y_x(u) = true`):
`PN = (P(y) - P(y | do(x'))) / P(x, y)`. `SCM.cfProb_necessity_eq` rewrites this as the
right-hand side of eq. (54). -/
theorem cfProb_necessity [Fintype β] (s : SCM Bool β n) (i j : Fin n)
    (hmono : ∀ u, s.counterfactual {i} (fun _ => false) u j = true →
      s.counterfactual {i} (fun _ => true) u j = true)
    (hxy : 0 < ∑ x with x i = true ∧ x j = true, s.law x) :
    s.cfProb {i} (fun _ => false) (fun x => x i = true ∧ x j = true) hxy (fun x => x j = false) =
      ((∑ x with x j = true, s.law x) - ∑ x with x j = true, (s.doSet {i} fun _ => false).law x) /
        ∑ x with x i = true ∧ x j = true, s.law x := by
  rw [sum_law_filter, sum_law_filter, sum_law_filter, cfProb, doSet_noise, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun u _ => ?_
  rw [← mul_sub]
  congr 1
  change _ = _ - (if s.counterfactual {i} (fun _ => false) u j = true then 1 else 0)
  by_cases hX : s.solve u i = true
  · have h1 : s.counterfactual {i} (fun _ => true) u = s.solve u :=
      s.counterfactual_eq_solve (by simpa using hX)
    have hm := hmono u
    rw [h1] at hm
    cases hY0 : s.counterfactual {i} (fun _ => false) u j <;> cases hY : s.solve u j <;>
      simp_all
  · have hX' : s.solve u i = false := by simpa using hX
    have h0 : s.counterfactual {i} (fun _ => false) u = s.solve u :=
      s.counterfactual_eq_solve (by simpa using hX')
    rw [h0]
    simp [hX]

/-- **Pearl's formula for the probability of necessity** (Pearl, *Statistics Surveys* 2009,
Theorem 3, eq. (54)): under monotonicity, and when `P(x, y) > 0`,
`PN = (P(y|x) - P(y|x')) / P(y|x) + (P(y|x') - P(y | do(x'))) / P(x, y)`: the excess risk ratio
plus a correction for confounding. -/
theorem cfProb_necessity_eq [Fintype β] (s : SCM Bool β n) (i j : Fin n)
    (hmono : ∀ u, s.counterfactual {i} (fun _ => false) u j = true →
      s.counterfactual {i} (fun _ => true) u j = true)
    (hxy : 0 < ∑ x with x i = true ∧ x j = true, s.law x) :
    s.cfProb {i} (fun _ => false) (fun x => x i = true ∧ x j = true) hxy (fun x => x j = false) =
      ((∑ x with x i = true ∧ x j = true, s.law x) / (∑ x with x i = true, s.law x) -
          (∑ x with x i = false ∧ x j = true, s.law x) / (∑ x with x i = false, s.law x)) /
        ((∑ x with x i = true ∧ x j = true, s.law x) / (∑ x with x i = true, s.law x)) +
      ((∑ x with x i = false ∧ x j = true, s.law x) / (∑ x with x i = false, s.law x) -
          ∑ x with x j = true, (s.doSet {i} fun _ => false).law x) /
        ∑ x with x i = true ∧ x j = true, s.law x := by
  rw [s.cfProb_necessity i j hmono hxy]
  have h0 : ∀ x, 0 ≤ s.law x := fun x => by
    rw [law_eq_joint]
    exact s.toBayesNet.toChain.joint_nonneg n x
  set a := ∑ x with x i = true ∧ x j = true, s.law x
  set b := ∑ x with x i = false ∧ x j = true, s.law x
  set px := ∑ x with x i = true, s.law x
  set px' := ∑ x with x i = false, s.law x
  set c := ∑ x with x j = true, (s.doSet {i} fun _ => false).law x
  have hy : ∑ x with x j = true, s.law x = a + b := by
    rw [← sum_filter_add_sum_filter_not (univ.filter fun x : Fin n → Bool => x j = true)
      (fun x => x i = true), filter_filter, filter_filter]
    congr 1
    · exact sum_congr (filter_congr fun x _ => and_comm) fun _ _ => rfl
    · refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
      simp only [Bool.not_eq_true]
      exact and_comm
  have hp : px + px' = 1 := by
    rw [← s.sum_law, ← sum_filter_add_sum_filter_not univ (fun x : Fin n → Bool => x i = true)]
    congr 1
  have ha0 : 0 < a := hxy
  have hapx : a ≤ px := sum_le_sum_of_subset_of_nonneg
    (fun x hx => by simp only [mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.1⟩) fun x _ _ => h0 x
  have hbpx : b ≤ px' := sum_le_sum_of_subset_of_nonneg
    (fun x hx => by simp only [mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.1⟩) fun x _ _ => h0 x
  have hb0 : 0 ≤ b := sum_nonneg fun x _ => h0 x
  have hpx : 0 < px := lt_of_lt_of_le ha0 hapx
  rw [hy]
  by_cases hpx' : px' = 0
  · have hb : b = 0 := le_antisymm (hpx' ▸ hbpx) hb0
    rw [hpx', hb]
    field_simp
    ring
  · have hpxe : px = 1 - px' := by linarith
    rw [hpxe] at hpx ⊢
    field_simp
    ring

end SCM

end Cslib.MachineLearning.GraphicalModels
