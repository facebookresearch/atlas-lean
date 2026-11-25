/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sampling.BayesNetGibbs
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Tests for Gibbs sampling on Bayesian-network posteriors

Collider `0 → 2 ← 1` over `Bool` with strictly positive tables and evidence `X₂ = true`.
The full conditional of `X₀` given the blanket exhibits explaining away:
`P(X₀ = true | X₁ = false, X₂ = true) = 15/19` but
`P(X₀ = true | X₁ = true, X₂ = true) = 9/25`.
These exact values would catch a `blanketFactor` missing the child or co-parent factor.
-/

@[expose] public section

namespace Cslib.MachineLearning.BayesNetGibbsTests

open Cslib.MachineLearning.GraphicalModels Cslib.MachineLearning.Sampling Finset Convexity

/-- A biased coin with `P(true) = p`. -/
noncomputable def gibbsCoin (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Convexity.StdSimplex ℝ Bool :=
  Convexity.StdSimplex.duple true false hp0 (sub_nonneg.mpr hp1) (by linarith)

/-- Parents for the collider `0 → 2 ← 1`. -/
def colliderPa : (k : Fin 3) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => ∅
  | ⟨2, _⟩ => {0, 1}
  | ⟨_ + 3, h⟩ => absurd h (by omega)

/-- Tables: `P(X₀ = true) = 1/3`, `P(X₁ = true) = 2/5`, and `P(X₂ = true | x₀, x₁)` is
`1/10, 3/4, 4/5, 9/10` for `(x₀, x₁) = (false,false), (true,false), (false,true),
(true,true)`. -/
noncomputable def colliderCpt : (k : Fin 3) → (colliderPa k → Bool) → StdSimplex ℝ Bool
  | ⟨0, _⟩, _ => gibbsCoin (1/3) (by norm_num) (by norm_num)
  | ⟨1, _⟩, _ => gibbsCoin (2/5) (by norm_num) (by norm_num)
  | ⟨2, _⟩, u => gibbsCoin
      (if u ⟨0, by simp [colliderPa]⟩ then (if u ⟨1, by simp [colliderPa]⟩ then 9/10 else 3/4)
       else (if u ⟨1, by simp [colliderPa]⟩ then 4/5 else 1/10))
      (by split <;> split <;> norm_num) (by split <;> split <;> norm_num)
  | ⟨_ + 3, h⟩, _ => absurd h (by omega)

/-- The collider net. -/
noncomputable def colliderNet : BayesNet Bool 3 := ⟨colliderPa, colliderCpt⟩

/-- All collider tables are strictly positive. -/
theorem colliderNet_positive : colliderNet.PositiveCPT := by
  intro k
  fin_cases k
  · intro u a
    cases a <;>
      simp [colliderNet, colliderCpt, gibbsCoin, Convexity.StdSimplex.weights_duple,
        Finsupp.add_apply]
    norm_num
  · intro u a
    cases a <;>
      simp [colliderNet, colliderCpt, gibbsCoin, Convexity.StdSimplex.weights_duple,
        Finsupp.add_apply]
    norm_num
  · intro u a
    cases a <;>
      simp [colliderNet, colliderCpt, gibbsCoin, Convexity.StdSimplex.weights_duple,
        Finsupp.add_apply] <;>
      split <;> split <;> norm_num

/-- The Markov blanket of `0` is its child `2` and its co-parent `1`. -/
theorem colliderNet_blanket_zero : colliderNet.markovBlanket 0 = {1, 2} := by
  ext j
  fin_cases j <;> decide

/-- Free coordinate `0` given evidence `{2}`. -/
def colliderFree0 : {i : Fin 3 // i ∉ ({2} : Finset (Fin 3))} := ⟨0, by decide⟩

/-- Free assignment with `X₁ = b` (the value at `0` is overwritten by updates). -/
def colliderZ (b : Bool) : {i : Fin 3 // i ∉ ({2} : Finset (Fin 3))} → Bool :=
  fun i => if i.1 = 1 then b else false

/-- `P(X₀ = true | X₁ = false, X₂ = true) = 15/19`. -/
theorem collider_condLaw_false :
    (condLaw (colliderNet.posteriorFree {2} (fun _ => true)
        (colliderNet.evidenceProb_ne_zero colliderNet_positive {2} (fun _ => true)))
      (BayesNet.posteriorFree_ne_zero colliderNet_positive {2} (fun _ => true)
        (colliderNet.evidenceProb_ne_zero colliderNet_positive {2} (fun _ => true)))
      colliderFree0 (colliderZ false) true).toReal = 15 / 19 := by
  rw [BayesNet.condLaw_posteriorFree_apply_toReal colliderNet_positive]
  have hc0 : colliderFree0.1 = (0 : Fin 3) := rfl
  have hfilter : Finset.univ.filter (colliderNet.Edge 0) = {2} := by decide
  have hx0t : extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ false) colliderFree0 true) 0 = true := by decide
  have hx1t : extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ false) colliderFree0 true) 1 = false := by decide
  have hx2t : extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ false) colliderFree0 true) 2 = true := by decide
  have hx0f : extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ false) colliderFree0 false) 0 = false := by decide
  have hx1f : extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ false) colliderFree0 false) 1 = false := by decide
  have hx2f : extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ false) colliderFree0 false) 2 = true := by decide
  simp only [hc0, BayesNet.blanketFactor, hfilter, Finset.prod_singleton, Fintype.sum_bool]
  have hf0t : colliderNet.cptFactor 0 (extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ false) colliderFree0 true)) = 1/3 := by
    show (gibbsCoin (1/3) (by norm_num) (by norm_num)).weights
        ((extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ false) colliderFree0 true)) 0) = 1/3
    simp [hx0t, gibbsCoin, Convexity.StdSimplex.weights_duple, Finsupp.add_apply]
  have hf2t : colliderNet.cptFactor 2 (extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ false) colliderFree0 true)) = 3/4 := by
    show (gibbsCoin (if (extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ false) colliderFree0 true)) 0
        then (if (extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ false) colliderFree0 true)) 1
          then (9/10 : ℝ) else 3/4)
        else (if (extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ false) colliderFree0 true)) 1
          then 4/5 else 1/10))
        (by split <;> split <;> norm_num) (by split <;> split <;> norm_num)).weights
        ((extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ false) colliderFree0 true)) 2) = 3/4
    simp [hx0t, hx1t, hx2t, gibbsCoin, Convexity.StdSimplex.weights_duple,
      Finsupp.add_apply]
  have hf0f : colliderNet.cptFactor 0 (extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ false) colliderFree0 false)) = 2/3 := by
    show (gibbsCoin (1/3) (by norm_num) (by norm_num)).weights
        ((extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ false) colliderFree0 false)) 0) = 2/3
    simp [hx0f, gibbsCoin, Convexity.StdSimplex.weights_duple, Finsupp.add_apply]
    norm_num
  have hf2f : colliderNet.cptFactor 2 (extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ false) colliderFree0 false)) = 1/10 := by
    show (gibbsCoin (if (extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ false) colliderFree0 false)) 0
        then (if (extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ false) colliderFree0 false)) 1
          then (9/10 : ℝ) else 3/4)
        else (if (extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ false) colliderFree0 false)) 1
          then 4/5 else 1/10))
        (by split <;> split <;> norm_num) (by split <;> split <;> norm_num)).weights
        ((extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ false) colliderFree0 false)) 2) = 1/10
    simp [hx0f, hx1f, hx2f, gibbsCoin, Convexity.StdSimplex.weights_duple,
      Finsupp.add_apply]
  rw [hf0t, hf2t, hf0f, hf2f]
  norm_num

/-- `P(X₀ = true | X₁ = true, X₂ = true) = 9/25`; explaining away lowers it. -/
theorem collider_condLaw_true :
    (condLaw (colliderNet.posteriorFree {2} (fun _ => true)
        (colliderNet.evidenceProb_ne_zero colliderNet_positive {2} (fun _ => true)))
      (BayesNet.posteriorFree_ne_zero colliderNet_positive {2} (fun _ => true)
        (colliderNet.evidenceProb_ne_zero colliderNet_positive {2} (fun _ => true)))
      colliderFree0 (colliderZ true) true).toReal = 9 / 25 := by
  rw [BayesNet.condLaw_posteriorFree_apply_toReal colliderNet_positive]
  have hc0 : colliderFree0.1 = (0 : Fin 3) := rfl
  have hfilter : Finset.univ.filter (colliderNet.Edge 0) = {2} := by decide
  have hx0t : extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ true) colliderFree0 true) 0 = true := by decide
  have hx1t : extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ true) colliderFree0 true) 1 = true := by decide
  have hx2t : extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ true) colliderFree0 true) 2 = true := by decide
  have hx0f : extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ true) colliderFree0 false) 0 = false := by decide
  have hx1f : extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ true) colliderFree0 false) 1 = true := by decide
  have hx2f : extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ true) colliderFree0 false) 2 = true := by decide
  simp only [hc0, BayesNet.blanketFactor, hfilter, Finset.prod_singleton, Fintype.sum_bool]
  have hf0t : colliderNet.cptFactor 0 (extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ true) colliderFree0 true)) = 1/3 := by
    show (gibbsCoin (1/3) (by norm_num) (by norm_num)).weights
        ((extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ true) colliderFree0 true)) 0) = 1/3
    simp [hx0t, gibbsCoin, Convexity.StdSimplex.weights_duple, Finsupp.add_apply]
  have hf2t : colliderNet.cptFactor 2 (extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ true) colliderFree0 true)) = 9/10 := by
    show (gibbsCoin (if (extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ true) colliderFree0 true)) 0
        then (if (extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ true) colliderFree0 true)) 1
          then (9/10 : ℝ) else 3/4)
        else (if (extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ true) colliderFree0 true)) 1
          then 4/5 else 1/10))
        (by norm_num [hx0t, hx1t]) (by norm_num [hx0t, hx1t])).weights
        ((extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ true) colliderFree0 true)) 2) = 9/10
    simp [hx0t, hx1t, hx2t, gibbsCoin, Convexity.StdSimplex.weights_duple,
      Finsupp.add_apply]
  have hf0f : colliderNet.cptFactor 0 (extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ true) colliderFree0 false)) = 2/3 := by
    show (gibbsCoin (1/3) (by norm_num) (by norm_num)).weights
        ((extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ true) colliderFree0 false)) 0) = 2/3
    simp [hx0f, gibbsCoin, Convexity.StdSimplex.weights_duple, Finsupp.add_apply]
    norm_num
  have hf2f : colliderNet.cptFactor 2 (extendEvidence {2} (fun _ => true)
      (Function.update (colliderZ true) colliderFree0 false)) = 4/5 := by
    show (gibbsCoin (if (extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ true) colliderFree0 false)) 0
        then (if (extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ true) colliderFree0 false)) 1
          then (9/10 : ℝ) else 3/4)
        else (if (extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ true) colliderFree0 false)) 1
          then 4/5 else 1/10))
        (by norm_num [hx0f, hx1f]) (by norm_num [hx0f, hx1f])).weights
        ((extendEvidence {2} (fun _ => true)
          (Function.update (colliderZ true) colliderFree0 false)) 2) = 4/5
    simp [hx0f, hx1f, hx2f, gibbsCoin, Convexity.StdSimplex.weights_duple,
      Finsupp.add_apply]
  rw [hf0t, hf2t, hf0f, hf2f]
  norm_num

end Cslib.MachineLearning.BayesNetGibbsTests
