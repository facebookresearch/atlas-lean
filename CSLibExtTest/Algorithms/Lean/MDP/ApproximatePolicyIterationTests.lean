/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.ApproximatePolicyIteration
public meta import CSLibExt.Algorithms.Lean.MDP.ApproximatePolicyIteration
public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fin.VecNotation
public meta import Mathlib.Data.Fin.VecNotation

/-!
# Approximate policy iteration: tests

Executed fixtures over `ℚ` on the maintenance MDP of the value-iteration tests (three states, two
actions, `γ = 9/10`, optimal policy `![0, 1, 1]`). Each run performs approximate policy iteration
with an evaluation `J k = V^{μ k} + e k`, where the perturbations `e k` cycle through a fixed list
with `|e k s| ≤ δ`, takes `μ (k + 1)` greedy for `J k`, evaluates every policy exactly, and checks
in every state and at every step the bound
`V*(s) - V^{μ k}(s) ≤ γ ^ k ‖V* - V^{μ 0}‖∞ + 2 γ δ / (1 - γ) ^ 2`
(`optimalValue_sub_policyValue_approxPI_le`), the one-step loss bound
(`policyValue_sub_policyValue_succ_le`), and, whenever the greedy policy repeats, the stopping bound
`2 γ δ / (1 - γ)` (`optimalValue_sub_policyValue_le_of_greedy`); it throws otherwise.

Closed checks over `ℝ`: the hypotheses hold for exact policy iteration (`δ = 0`) and for the
non-degenerate evaluation `J k = V^{μ k} + 1` (`δ = 1`) of an arbitrary stochastic MDP.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

private abbrev St := Fin 3
private abbrev Ac := Fin 2

private meta def machine : MDP St Ac ℚ where
  reward := ![![3, 1], ![2, 0], ![-1, -4]]
  prob := ![![![1/2, 1/2, 0], ![1, 0, 0]],
    ![![0, 1/2, 1/2], ![3/4, 1/4, 0]],
    ![![0, 0, 1], ![1/2, 1/2, 0]]]

private meta def γm : ℚ := 9 / 10
private meta def sts : List St := List.finRange 3

/-- Solve `(I - γ P_π) V = r_π` exactly by Gauss-Jordan elimination. -/
private meta def evaluate (π : St → Ac) : St → ℚ := Id.run do
  let n := 3
  let mut m : Array (Array ℚ) := sts.toArray.map fun i =>
    (sts.toArray.map fun j => (if i = j then 1 else 0) - γm * machine.prob i (π i) j).push
      (machine.reward i (π i))
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

/-- A greedy policy: the first action of largest value. -/
private meta def greedyQ (V : St → ℚ) : St → Ac := fun s =>
  if qValue machine γm V s 1 > qValue machine γm V s 0 then 1 else 0

private meta def supNorm (V : St → ℚ) : ℚ := sts.foldl (fun m s => max m (abs (V s))) 0

#eval do
  let Vs := evaluate ![0, 1, 1]
  unless sts.all fun s => bellman machine γm Vs s == Vs s do
    throw (IO.userError "![0, 1, 1] is not optimal")
  let mut checks := 0
  for δ in [(1 : ℚ) / 10, 1, 3, 10] do
    let errs : List (St → ℚ) := [![δ, -δ, δ], ![-δ, δ, 0], ![0, δ, -δ], ![δ, δ, δ], ![-δ, 0, δ]]
    for π0 in [(![0, 0, 0] : St → Ac), ![1, 1, 1], ![1, 0, 0], ![0, 1, 0]] do
      let V0 := evaluate π0
      let d0 := supNorm fun s => Vs s - V0 s
      let mut μ := π0
      for k in [0:12] do
        let V := evaluate μ
        for s in sts do
          unless Vs s - V s ≤ γm ^ k * d0 + 2 * γm * δ / (1 - γm) ^ 2 do
            throw (IO.userError s!"API bound fails at step {k}, δ = {δ}")
          checks := checks + 1
        let e := errs.getD (k % errs.length) (fun _ => 0)
        let J : St → ℚ := fun s => V s + e s
        -- tabulate the new policy, so that later steps do not re-run earlier evaluations
        let tab := sts.map (greedyQ J)
        let μ' : St → Ac := fun s => tab.getD s.val 0
        let V' := evaluate μ'
        for s in sts do
          unless V s - V' s ≤ 2 * γm * δ / (1 - γm) do
            throw (IO.userError s!"one-step loss bound fails at step {k}, δ = {δ}")
        if sts.all fun s => μ' s == μ s then
          for s in sts do
            unless 0 ≤ Vs s - V s ∧ Vs s - V s ≤ 2 * γm * δ / (1 - γm) do
              throw (IO.userError s!"stopping bound fails at step {k}, δ = {δ}")
        μ := μ'
  IO.println s!"approximate policy iteration: {checks} exact checks passed"

/-! Closed checks over `ℝ` -/

section Closed

variable (M : MDP St Ac ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)

/-- Exact policy iteration satisfies the hypotheses with `δ = 0`. -/
example (π : St → Ac) (k : ℕ) (s : St) :
    optimalValue M γ hM hγ0 hγ1 s -
        policyValue M γ hM hγ0 hγ1 (policyIteration hM hγ0 hγ1 k π) s ≤
      γ ^ k * dist (optimalValue M γ hM hγ0 hγ1)
          (policyValue M γ hM hγ0 hγ1 (policyIteration hM hγ0 hγ1 0 π)) +
        2 * γ * 0 / (1 - γ) ^ 2 :=
  optimalValue_sub_policyValue_approxPI_le hM hγ0 hγ1
    (μ := fun k => policyIteration hM hγ0 hγ1 k π)
    (J := fun k => policyValue M γ hM hγ0 hγ1 (policyIteration hM hγ0 hγ1 k π))
    (fun k s => by simp)
    (fun k => by
      simp only [policyIteration, Function.iterate_succ_apply']
      exact policyBellman_greedy _) k s

/-- A non-degenerate evaluation error: `J k = V^{μ k} + 1`, `δ = 1`. -/
private noncomputable def shiftedPI (π : St → Ac) : ℕ → St → Ac
  | 0 => π
  | k + 1 => greedy M γ fun s => policyValue M γ hM hγ0 hγ1 (shiftedPI π k) s + 1

example (π : St → Ac) :
    Filter.limsup (fun k => dist (optimalValue M γ hM hγ0 hγ1)
      (policyValue M γ hM hγ0 hγ1 (shiftedPI M γ hM hγ0 hγ1 π k))) Filter.atTop ≤
      2 * γ * 1 / (1 - γ) ^ 2 :=
  limsup_dist_optimalValue_policyValue_le hM hγ0 hγ1
    (μ := shiftedPI M γ hM hγ0 hγ1 π)
    (J := fun k s => policyValue M γ hM hγ0 hγ1 (shiftedPI M γ hM hγ0 hγ1 π k) s + 1)
    (fun k s => by simp)
    (fun k => policyBellman_greedy _)

/-- The stopping bound, for a policy greedy for its own value shifted by `1`. -/
example (μ : St → Ac)
    (hμ : policyBellman M γ μ (fun s => policyValue M γ hM hγ0 hγ1 μ s + 1) =
      bellman M γ (fun s => policyValue M γ hM hγ0 hγ1 μ s + 1)) (s : St) :
    optimalValue M γ hM hγ0 hγ1 s - policyValue M γ hM hγ0 hγ1 μ s ≤ 2 * γ * 1 / (1 - γ) :=
  (optimalValue_sub_policyValue_le_of_greedy hM hγ0 hγ1 (fun s => by simp) hμ s).2

end Closed

#print axioms optimalValue_sub_policyValue_le_of_greedy
#print axioms policyValue_sub_policyValue_succ_le
#print axioms optimalValue_sub_policyValue_approxPI_le
#print axioms limsup_dist_optimalValue_policyValue_le

end Cslib.Algorithms.Lean.MarkovDecision
