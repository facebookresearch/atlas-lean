/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.ValueIteration
public meta import CSLibExt.Algorithms.Lean.MDP.ValueIteration
public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fin.VecNotation
public meta import Mathlib.Data.Fin.VecNotation

/-!
# Value iteration tests

Executed fixtures over `ℚ` (the operators are defined over any ordered field). A three-state,
two-action maintenance MDP with `γ = 9/10`, whose eight deterministic policies have exact values
computed offline: the optimal value `V* = (930/49, 810/49, 587/49)` solves the Bellman optimality
equation exactly, every policy value solves its own Bellman equation and lies below `V*`, value
iteration from `0` by `valueIterationVec` (equal to `valueIteration` for `n ≤ 5`) stays within the a
priori bound `‖V - T V‖ γ ^ n / (1 - γ)` and the stopping-test bound of `V*` for `n ≤ 40`, and the
Bellman operator contracts by `γ` on pseudo-random pairs (`abs_bellman_sub_le`). A one-state MDP
checks the bound is attained. Each run throws on failure. Closed checks instantiate the theorems
over `ℝ`.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

private abbrev St := Fin 3
private abbrev Ac := Fin 2

/-- States: good, worn, broken; actions: run, repair. -/
private meta def machine : MDP St Ac ℚ where
  reward := ![![3, 1], ![2, 0], ![-1, -4]]
  prob := ![![![1/2, 1/2, 0], ![1, 0, 0]],
    ![![0, 1/2, 1/2], ![3/4, 1/4, 0]],
    ![![0, 0, 1], ![1/2, 1/2, 0]]]

private meta def γm : ℚ := 9 / 10

/-- The sup distance on `Fin n → ℚ`. -/
private meta def supDist {n : ℕ} (V W : Fin n → ℚ) : ℚ :=
  (List.finRange n).foldl (fun m s => max m |V s - W s|) 0

private meta def showV {n : ℕ} {β : Type} (V : Fin n → β) : List β := (List.finRange n).map V

/-- Exact values of the eight policies (run = 0, repair = 1), computed offline. -/
private meta def policies : List ((St → Ac) × (St → ℚ)) :=
  [(![0, 0, 0], ![210/121, -50/11, -10]), (![0, 0, 1], ![453/40, 287/40, 173/40]),
    (![0, 1, 0], ![930/49, 810/49, -10]), (![0, 1, 1], ![930/49, 810/49, 587/49]),
    (![1, 0, 0], ![10, -50/11, -10]), (![1, 0, 1], ![10, 890/139, 470/139]),
    (![1, 1, 0], ![10, 270/31, -10]), (![1, 1, 1], ![10, 270/31, 137/31])]

private meta def Vstar : St → ℚ := ![930/49, 810/49, 587/49]

#eval do
  unless supDist (bellman machine γm Vstar) Vstar == 0 do
    throw (IO.userError "V* does not solve the Bellman equation")
  for (π, V) in policies do
    unless supDist (policyBellman machine γm π V) V == 0 do
      throw (IO.userError s!"policy {showV π}: value does not solve its Bellman equation")
    unless (List.finRange 3).all fun s => V s ≤ Vstar s do
      throw (IO.userError s!"policy {showV π} beats V*")
  IO.println s!"maintenance MDP: V* = {showV Vstar} solves T V = V; all 8 policy values solve \
    their equations and lie below V*"

#eval do
  let V0 : St → ℚ := 0
  let c := supDist V0 (bellman machine γm V0)
  for n in [0:41] do
    let v := valueIterationVec machine γm n (Vector.ofFn V0)
    let Vn : St → ℚ := fun s => v.get s
    if n ≤ 5 then
      unless supDist Vn (valueIteration machine γm n V0) == 0 do
        throw (IO.userError s!"step {n}: valueIterationVec differs from valueIteration")
    let err := supDist Vn Vstar
    unless err ≤ c * γm ^ n / (1 - γm) do
      throw (IO.userError s!"value iteration step {n}: distance {err} above the a priori bound")
    unless err ≤ supDist Vn (bellman machine γm Vn) / (1 - γm) do
      throw (IO.userError s!"value iteration step {n}: distance above the stopping-test bound")
  IO.println s!"valueIterationVec from 0 (equal to valueIteration for n ≤ 5): within the a priori \
    and stopping-test bounds for n ≤ 40"

/-- Pseudo-random value functions with entries in `[-20, 20]`. -/
private meta def randV (s : ℕ) : (St → ℚ) × ℕ :=
  let n1 := (s * 1103515245 + 12345) % 2147483648
  let n2 := (n1 * 1103515245 + 12345) % 2147483648
  let n3 := (n2 * 1103515245 + 12345) % 2147483648
  (![((n1 / 7 % 41 : ℕ) : ℚ) - 20, ((n2 / 7 % 41 : ℕ) : ℚ) - 20, ((n3 / 7 % 41 : ℕ) : ℚ) - 20], n3)

#eval do
  let mut s := 1
  for _ in [0:200] do
    let (V, s1) := randV s
    let (W, s2) := randV s1
    s := s2
    let d := supDist V W
    unless supDist (bellman machine γm V) (bellman machine γm W) ≤ γm * d do
      throw (IO.userError s!"contraction fails at {showV V}, {showV W}")
  IO.println "Bellman operator contracts by γ = 9/10 on 200 pseudo-random pairs"

-- One state, actions worth 1 and 2: V* = 2 / (1 - 1/2) = 4, and the a priori bound is attained.
#eval do
  let M : MDP (Fin 1) Ac ℚ := ⟨fun _ a => if a = 0 then 1 else 2, fun _ _ _ => 1⟩
  let g : ℚ := 1 / 2
  unless bellman M g (fun _ => 4) 0 == 4 do throw (IO.userError "one state: V* ≠ 4")
  for n in [0:8] do
    let err := |valueIteration M g n 0 0 - 4|
    unless err == 2 * g ^ n / (1 - g) do
      throw (IO.userError s!"one state, step {n}: error {err}")
  IO.println "one state: distance to V* after n steps is exactly 4 / 2^n, the a priori bound"

/-! Closed checks over `ℝ` -/

example (M : MDP St Ac ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : St → Ac) : policyValue M γ hM hγ0 hγ1 π ≤ optimalValue M γ hM hγ0 hγ1 :=
  policyValue_le_optimalValue hM hγ0 hγ1 π

example (M : MDP St Ac ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : St → Ac) (V : St → ℝ) (hV : policyBellman M γ π V = V) :
    V = policyValue M γ hM hγ0 hγ1 π ∧
      policyBellman M γ π (policyValue M γ hM hγ0 hγ1 π) = policyValue M γ hM hγ0 hγ1 π :=
  ⟨eq_policyValue_of_policyBellman_eq hM hγ0 hγ1 π hV, policyBellman_policyValue hM hγ0 hγ1 π⟩

#print axioms valueIterationVec_get
#print axioms bellman_contracting
#print axioms policyBellman_policyValue
#print axioms eq_policyValue_of_policyBellman_eq
#print axioms tendsto_valueIteration
#print axioms dist_valueIteration_le
#print axioms dist_optimalValue_le
#print axioms eq_optimalValue_of_bellman_eq
#print axioms policyValue_le_optimalValue
#print axioms policyValue_greedy

end Cslib.Algorithms.Lean.MarkovDecision
