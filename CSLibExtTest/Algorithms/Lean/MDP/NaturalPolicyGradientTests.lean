/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.NaturalPolicyGradient
public meta import CSLibExt.Algorithms.Lean.MDP.NaturalPolicyGradient

/-!
# Natural policy gradient tests

A floating-point simulation of the softmax NPG iteration `θ_{t+1} = θ_t + η / (1 - γ) A^{π_t}`
(`npgLogits`) on the maintenance MDP of the value-iteration tests, with rewards rescaled to
`[0, 1]` (`(r + 4) / 7`) and `γ = 9/10`. Policies are evaluated by Gauss-Jordan elimination and
the optimal value by value iteration followed by evaluation of the greedy policy. For
`η ∈ {1/10, 1, 10}` and `T ≤ 200` the run checks, up to `10⁻⁹`, that values never decrease
(`stochValue_npgPolicy_mono`) and that
`V*(s) - V^{(T)}(s) ≤ log |A| / (η T) + 1 / ((1 - γ)² T)` in every state
(`optimalValue_sub_stochValue_npgPolicy_le`); it throws otherwise. This is a numerical
diagnostic: the theorem itself is proved over `ℝ`. Closed checks instantiate the theorems.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision.Simplex

private meta def nS : Nat := 3
private meta def nA : Nat := 2
private meta def γf : Float := 0.9

private meta def rewardF (s a : Nat) : Float :=
  let r : List (List Float) := [[3, 1], [2, 0], [-1, -4]]
  ((r.getD s []).getD a 0 + 4) / 7

private meta def probF (s a s' : Nat) : Float :=
  let p : List (List (List Float)) := [[[0.5, 0.5, 0], [1, 0, 0]],
    [[0, 0.5, 0.5], [0.75, 0.25, 0]], [[0, 0, 1], [0.5, 0.5, 0]]]
  ((p.getD s []).getD a []).getD s' 0

private meta def sumN (n : Nat) (f : Nat → Float) : Float :=
  (List.range n).foldl (fun x i => x + f i) 0

/-- Solve `(I - γ K) x = b` by Gauss-Jordan elimination with partial pivoting. -/
private meta def solveF (K : Nat → Nat → Float) (b : Nat → Float) : Array Float := Id.run do
  let n := nS
  let mut m : Array (Array Float) := (List.range n).toArray.map fun i =>
    ((List.range n).toArray.map fun j => (if i = j then 1 else 0) - γf * K i j).push (b i)
  for c in [0:n] do
    let mut p := c
    for r in [c:n] do
      if ((m.getD r #[]).getD c 0).abs > ((m.getD p #[]).getD c 0).abs then p := r
    let tmp := m.getD c #[]
    m := (m.set! c (m.getD p #[])).set! p tmp
    let pivot := ((m.getD c #[]).getD c 0)
    m := m.set! c ((m.getD c #[]).map (· / pivot))
    for r in [0:n] do
      if r != c then
        let f := ((m.getD r #[]).getD c 0)
        m := m.set! r (((m.getD r #[]).zip (m.getD c #[])).map fun (x, y) => x - f * y)
  return (List.range n).toArray.map fun i => ((m.getD i #[]).getD n 0)

private meta def softmaxF (θ : Array (Array Float)) (s a : Nat) : Float :=
  let row := θ.getD s #[]
  Float.exp (row.getD a 0) / sumN nA fun b => Float.exp (row.getD b 0)

private meta def valueF (π : Nat → Nat → Float) : Array Float :=
  solveF (fun s s' => sumN nA fun a => π s a * probF s a s')
    (fun s => sumN nA fun a => π s a * rewardF s a)

private meta def qF (V : Array Float) (s a : Nat) : Float :=
  rewardF s a + γf * sumN nS fun s' => probF s a s' * V.getD s' 0

private meta def optimalF : Array Float := Id.run do
  let mut V : Array Float := #[0, 0, 0]
  for _ in [0:3000] do
    V := (List.range nS).toArray.map fun s => max (qF V s 0) (qF V s 1)
  let greedy : Nat → Nat → Float := fun s a =>
    let best := if qF V s 1 > qF V s 0 then 1 else 0
    if a = best then 1 else 0
  return valueF greedy

#eval do
  let Vstar := optimalF
  let mut checks := 0
  for (η : Float) in [0.1, 1.0, 10.0] do
    let mut θ : Array (Array Float) := #[#[0, 0], #[0, 0], #[0, 0]]
    let mut Vprev : Array Float := valueF (softmaxF θ)
    for (T : Nat) in [1:201] do
      let V := valueF (softmaxF θ)
      θ := (List.range nS).toArray.map fun s => (List.range nA).toArray.map fun a =>
        (θ.getD s #[]).getD a 0 + η / (1 - γf) * (qF V s a - V.getD s 0)
      let V' := valueF (softmaxF θ)
      for s in List.range nS do
        unless V.getD s 0 ≤ V'.getD s 0 + 1e-9 do
          throw (IO.userError s!"η = {η}, T = {T}: NPG value decreased")
        let bound := Float.log 2 / (η * Nat.toFloat T) + 1 / ((1 - γf) ^ 2 * Nat.toFloat T)
        unless Vstar.getD s 0 - V'.getD s 0 ≤ bound + 1e-9 do
          throw (IO.userError s!"η = {η}, T = {T}: NPG convergence bound fails")
        checks := checks + 1
      Vprev := V'
    IO.println s!"η = {η}: gap after 200 NPG steps {(List.range nS).map fun s =>
      Vstar.getD s 0 - Vprev.getD s 0}"
  IO.println s!"natural policy gradient: {checks} floating-point checks passed"

/-! Closed checks over `ℝ` -/

example {M : MDP (Fin 3) (Fin 2) ℝ} {γ : ℝ} (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, 0 ≤ M.reward s a ∧ M.reward s a ≤ 1) (s : Fin 3) :
    optimalValue M γ hM hγ0 hγ1 s - stochValue M γ hM hγ0 hγ1 (npgPolicy hM hγ0 hγ1 1 10) s ≤
      Real.log (Fintype.card (Fin 2)) / (1 * (10 : ℕ)) + 1 / ((1 - γ) ^ 2 * (10 : ℕ)) :=
  optimalValue_sub_stochValue_npgPolicy_le hM hγ0 hγ1 hr one_pos (by norm_num) s

#print axioms npg_improvement
#print axioms optimalValue_sub_stochValue_npgPolicy_le

end Cslib.Algorithms.Lean.MarkovDecision.Simplex
