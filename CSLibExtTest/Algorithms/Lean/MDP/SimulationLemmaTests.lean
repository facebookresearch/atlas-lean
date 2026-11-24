/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.SimulationLemma
public meta import CSLibExt.Algorithms.Lean.MDP.SimulationLemma
public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fin.VecNotation
public meta import Mathlib.Data.Fin.VecNotation

/-!
# Simulation lemma tests

Executed fixtures over `ℚ`: the maintenance MDP of the value-iteration tests with rewards
rescaled to `[0, 1]` (`(r + 4) / 7`), `γ = 9/10`, and a perturbed model with the same rewards.
For six stochastic policies the run checks exactly the simulation identity
`V - V̂ = (I - γ P̂^π)⁻¹ (γ (P^π - P̂^π) V)` (`stochValue_sub_stochValue_eq`) and the bound
`|V(s) - V̂(s)| ≤ γ ε / (1 - γ)²` with `ε` the largest `ℓ¹` row error
(`abs_stochValue_sub_stochValue_le`); it throws otherwise. Closed checks instantiate the theorems.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision.Simplex

private abbrev St := Fin 3
private abbrev Ac := Fin 2

private meta def rewardQ : St → Ac → ℚ := fun s a => (![![3, 1], ![2, 0], ![-1, -4]] s a + 4) / 7

private meta def model : MDP St Ac ℚ where
  reward := rewardQ
  prob := ![![![1/2, 1/2, 0], ![1, 0, 0]],
    ![![0, 1/2, 1/2], ![3/4, 1/4, 0]],
    ![![0, 0, 1], ![1/2, 1/2, 0]]]

private meta def model' : MDP St Ac ℚ where
  reward := rewardQ
  prob := ![![![2/5, 1/2, 1/10], ![9/10, 1/10, 0]],
    ![![1/10, 1/2, 2/5], ![3/4, 1/5, 1/20]],
    ![![0, 1/10, 9/10], ![1/2, 2/5, 1/10]]]

private meta def γm : ℚ := 9 / 10
private meta def sts : List St := List.finRange 3
private meta def acs : List Ac := List.finRange 2
private meta def sumS (f : St → ℚ) : ℚ := sts.foldl (fun x s => x + f s) 0
private meta def sumA (f : Ac → ℚ) : ℚ := acs.foldl (fun x a => x + f a) 0

/-- Solve `(I - γ K) x = b` exactly by Gauss-Jordan elimination. -/
private meta def solve (K : St → St → ℚ) (b : St → ℚ) : St → ℚ := Id.run do
  let n := 3
  let mut m : Array (Array ℚ) := sts.toArray.map fun i =>
    (sts.toArray.map fun j => (if i = j then 1 else 0) - γm * K i j).push (b i)
  for c in [0:n] do
    let some p := (List.range' c (n - c)).find? (fun r => ((m.getD r #[]).getD c 0) != 0)
      | pure ()
    let tmp := m.getD c #[]
    m := (m.set! c (m.getD p #[])).set! p tmp
    let pivot := ((m.getD c #[]).getD c 0)
    m := m.set! c ((m.getD c #[]).map (· / pivot))
    for r in [0:n] do
      if r != c then
        let f := ((m.getD r #[]).getD c 0)
        m := m.set! r (((m.getD r #[]).zip (m.getD c #[])).map fun (x, y) => x - f * y)
  let t := (List.range n).map fun i => ((m.getD i #[]).getD n 0)
  return fun s => t.getD s.val 0

private meta def kernel (N : MDP St Ac ℚ) (σ : St → Ac → ℚ) (s s' : St) : ℚ :=
  sumA fun a => σ s a * N.prob s a s'

private meta def value (N : MDP St Ac ℚ) (σ : St → Ac → ℚ) : St → ℚ :=
  solve (kernel N σ) fun s => sumA fun a => σ s a * N.reward s a

private meta def dirac (π : St → Ac) : St → Ac → ℚ := fun s a => if a = π s then 1 else 0

private meta def policies : List (St → Ac → ℚ) :=
  [dirac ![0, 0, 0], dirac ![0, 1, 1], dirac ![1, 0, 1],
    fun _ _ => 1 / 2, ![![1/3, 2/3], ![1/4, 3/4], ![1, 0]], ![![0, 1], ![5/6, 1/6], ![1/2, 1/2]]]

#eval do
  let ε := sts.foldl (fun m s => acs.foldl (fun m a =>
    max m (sumS fun s' => |model.prob s a s' - model'.prob s a s'|)) m) 0
  let mut checks := 0
  for (σ : St → Ac → ℚ) in policies do
    let V := value model σ
    let V' := value model' σ
    let D := solve (kernel model' σ) fun s =>
      γm * sumS fun s' => (kernel model σ s s' - kernel model' σ s s') * V s'
    for s in sts do
      unless V s - V' s == D s do throw (IO.userError "simulation identity fails")
      unless |V s - V' s| ≤ γm * ε / (1 - γm) ^ 2 do throw (IO.userError "value bound fails")
      checks := checks + 1
  IO.println s!"simulation lemma: {checks} exact checks passed (ε = {ε})"

/-! Closed checks over `ℝ` -/

example {M M' : MDP St Ac ℝ} {γ : ℝ} (hM : M.Stochastic) (hM' : M'.Stochastic) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hr : M.reward = M'.reward)
    (hr01 : ∀ s a, 0 ≤ M.reward s a ∧ M.reward s a ≤ 1)
    (hε : ∀ s a, ∑ s', |M.prob s a s' - M'.prob s a s'| ≤ 1 / 10)
    (π : StochasticPolicy St Ac) (s : St) :
    |stochValue M γ hM hγ0 hγ1 π s - stochValue M' γ hM' hγ0 hγ1 π s| ≤
      γ * (1 / 10) / (1 - γ) ^ 2 :=
  abs_stochValue_sub_stochValue_le hM hM' hγ0 hγ1 hr hr01 hε π s

#print axioms stochValue_sub_stochValue_eq
#print axioms abs_stochValue_sub_stochValue_le

end Cslib.Algorithms.Lean.MarkovDecision.Simplex
