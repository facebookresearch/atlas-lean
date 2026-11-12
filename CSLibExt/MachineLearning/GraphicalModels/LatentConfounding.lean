/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CausalBayesNet

/-!
# Non-identifiability of causal effects under latent confounding

On the graph `U → X`, `U → Y`, `X → Y` with `U` latent, the observed law of `(X, Y)` does not
determine the interventional probability `P(Y = 1 | do(X = 1))`: two Bayesian networks on this
graph have the same `(X, Y)` marginal but different interventional probabilities. Interventions
are the surgery `BayesNet.intervene` of
`CSLibExt/MachineLearning/GraphicalModels/CausalBayesNet.lean`.

## Main definitions

* `OnConfoundedTriangle b`: the network `b : BayesNet Bool 3` has nodes `U = 0`, `X = 1`,
  `Y = 2` with parents `∅`, `{U}`, `{U, X}`.
* `observedLaw b x y`: `P(X = x, Y = y)` with `U` summed out.
* `doProb b x y`: `P(Y = y | do(X = x))`.

## Main results

* `exists_same_observedLaw_ne_doProb`: two networks on the graph, with `U` a fair coin and
  `X = U`, have the same observed law, but `P(Y = 1 | do(X = 1))` is `1` when `Y = X` (network
  `b₁`) and `1 / 2` when `Y = U` (network `b₂`).

The equality is of the `(X, Y)` marginal only, never of the full law including `U`.

## References

* J. Pearl, M. Glymour and N. P. Jewell, *Causal Inference in Statistics: A Primer*, Wiley
  (2016), ch. 3.
* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press
  (2009), §3.2.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels.LatentConfounding

open Cslib.MachineLearning.GraphicalModels

/-- `b` is a Bayesian network on the latent-confounding graph `U → X`, `U → Y`, `X → Y`, with
node order `U = 0` (latent), `X = 1`, `Y = 2`: `U` has no parents, `U` is the parent of `X`,
and `U`, `X` are the parents of `Y`. -/
def OnConfoundedTriangle (b : BayesNet Bool 3) : Prop :=
  b.pa 0 = ∅ ∧ b.pa 1 = Finset.univ ∧ b.pa 2 = Finset.univ

/-- The observed law `P(X = x, Y = y)`: the joint of the network with the latent `U` summed
out. -/
noncomputable def observedLaw (b : BayesNet Bool 3) (x y : Bool) : ℝ :=
  ∑ u : Bool, b.joint ![u, x, y]

/-- The interventional probability `P(Y = y | do(X = x))`: the joint of the intervened network
`b.intervene 1 x`, with `U` and `X` summed out. -/
noncomputable def doProb (b : BayesNet Bool 3) (x y : Bool) : ℝ :=
  ∑ u : Bool, ∑ x' : Bool, (b.intervene 1 x).joint ![u, x', y]

/-- Fair coin on `Bool`: each side has probability `1 / 2`. -/
noncomputable def fairCoin : Convexity.StdSimplex ℝ Bool where
  weights := Finsupp.equivFunOnFinite.symm (fun _ => (1 / 2 : ℝ))
  nonneg := fun _ => by
    simp
  total := by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl]
    simp

theorem fairCoin_weights (b : Bool) : fairCoin.weights b = 1 / 2 := by
  simp [fairCoin]

/-- Network 1: `U` fair, `X = U`, `Y = X`. -/
noncomputable def b₁ : BayesNet Bool 3 where
  pa := fun _ => Finset.univ
  cpt := fun k =>
    match k with
    | ⟨0, _⟩ => fun _ => fairCoin
    | ⟨1, _⟩ => fun z => Convexity.StdSimplex.single (z ⟨(0 : Fin 1), Finset.mem_univ _⟩)
    | ⟨2, _⟩ => fun z => Convexity.StdSimplex.single (z ⟨(1 : Fin 2), Finset.mem_univ _⟩)
    | ⟨_m + 3, _⟩ => fun _ => fairCoin

/-- Network 2: `U` fair, `X = U`, `Y = U`. -/
noncomputable def b₂ : BayesNet Bool 3 where
  pa := fun _ => Finset.univ
  cpt := fun k =>
    match k with
    | ⟨0, _⟩ => fun _ => fairCoin
    | ⟨1, _⟩ => fun z => Convexity.StdSimplex.single (z ⟨(0 : Fin 1), Finset.mem_univ _⟩)
    | ⟨2, _⟩ => fun z => Convexity.StdSimplex.single (z ⟨(0 : Fin 2), Finset.mem_univ _⟩)
    | ⟨_m + 3, _⟩ => fun _ => fairCoin

theorem b₁_joint (u x y : Bool) : b₁.joint ![u, x, y]
    = 1 / 2 * (if u = x then (1 : ℝ) else 0) * (if x = y then (1 : ℝ) else 0) := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_three]
  simp [b₁, fairCoin_weights, Finsupp.single_apply]

theorem b₂_joint (u x y : Bool) : b₂.joint ![u, x, y]
    = 1 / 2 * (if u = x then (1 : ℝ) else 0) * (if u = y then (1 : ℝ) else 0) := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_three]
  simp [b₂, fairCoin_weights, Finsupp.single_apply]

theorem b₁_observedLaw (x y : Bool) :
    observedLaw b₁ x y = if x = y then (1 / 2 : ℝ) else 0 := by
  cases x <;> cases y <;> simp [observedLaw, b₁_joint]

theorem b₂_observedLaw (x y : Bool) :
    observedLaw b₂ x y = if x = y then (1 / 2 : ℝ) else 0 := by
  cases x <;> cases y <;> simp [observedLaw, b₂_joint]

theorem b₁_intervene_joint (x u x' y : Bool) :
    (b₁.intervene 1 x).joint ![u, x', y]
      = if x' = x then 1 / 2 * (if x' = y then (1 : ℝ) else 0) else 0 := by
  rw [BayesNet.joint_intervene]
  have hidx : (![u, x', y] : Fin 3 → Bool) 1 = x' := by simp
  rw [hidx]
  by_cases h : x' = x
  · rw [ite_eq_left h, ite_eq_left h]
    have herase : Finset.univ.erase (1 : Fin 3) = {0, 2} := by decide
    have h01 : (0 : Fin 3) ∉ ({2} : Finset (Fin 3)) := by decide
    rw [herase, Finset.prod_insert h01, Finset.prod_singleton]
    simp [b₁, BayesNet.paVal, fairCoin_weights, Finsupp.single_apply]
  · rw [ite_eq_right h, ite_eq_right h]

theorem b₂_intervene_joint (x u x' y : Bool) :
    (b₂.intervene 1 x).joint ![u, x', y]
      = if x' = x then 1 / 2 * (if u = y then (1 : ℝ) else 0) else 0 := by
  rw [BayesNet.joint_intervene]
  have hidx : (![u, x', y] : Fin 3 → Bool) 1 = x' := by simp
  rw [hidx]
  by_cases h : x' = x
  · rw [ite_eq_left h, ite_eq_left h]
    have herase : Finset.univ.erase (1 : Fin 3) = {0, 2} := by decide
    have h01 : (0 : Fin 3) ∉ ({2} : Finset (Fin 3)) := by decide
    rw [herase, Finset.prod_insert h01, Finset.prod_singleton]
    simp [b₂, BayesNet.paVal, fairCoin_weights, Finsupp.single_apply]
  · rw [ite_eq_right h, ite_eq_right h]

theorem b₁_doProb_tt : doProb b₁ true true = 1 := by
  simp [doProb, b₁_intervene_joint]

theorem b₂_doProb_tt : doProb b₂ true true = 1 / 2 := by
  simp [doProb, b₂_intervene_joint]

theorem b₂_doProb_tf : doProb b₂ true false = 1 / 2 := by
  simp [doProb, b₂_intervene_joint]

theorem b₁_triangle : OnConfoundedTriangle b₁ := ⟨by decide, rfl, rfl⟩

theorem b₂_triangle : OnConfoundedTriangle b₂ := ⟨by decide, rfl, rfl⟩

/-- **Non-identifiability under latent confounding.** There are two Bayesian networks on the
graph `U → X`, `U → Y`, `X → Y` with `U` latent that have the same observed law of `(X, Y)`
but different interventional probabilities `P(Y = 1 | do(X = 1))`, namely `1` and `1 / 2`. -/
theorem exists_same_observedLaw_ne_doProb :
    ∃ b₁ b₂ : BayesNet Bool 3, OnConfoundedTriangle b₁ ∧ OnConfoundedTriangle b₂ ∧
      (∀ x y, observedLaw b₁ x y = observedLaw b₂ x y) ∧
      doProb b₁ true true = 1 ∧ doProb b₂ true true = 1 / 2 := by
  refine ⟨b₁, b₂, b₁_triangle, b₂_triangle, ?_, b₁_doProb_tt, b₂_doProb_tt⟩
  intro x y
  rw [b₁_observedLaw, b₂_observedLaw]

end Cslib.MachineLearning.GraphicalModels.LatentConfounding
