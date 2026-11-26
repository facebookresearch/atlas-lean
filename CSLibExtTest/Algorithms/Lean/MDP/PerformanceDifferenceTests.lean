/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.PerformanceDifference
public meta import CSLibExt.Algorithms.Lean.MDP.PerformanceDifference
public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fin.VecNotation
public meta import Mathlib.Data.Fin.VecNotation

/-!
# Stochastic policies, the performance difference lemma and CPI: tests

Executed fixtures over `ℚ`, on the maintenance MDP of the value-iteration tests (three states,
two actions, `γ = 9/10`). Stochastic policies are tables `σ s a`; a policy is evaluated by
solving `(I - γ P^σ) V = r^σ` exactly (Gauss-Jordan elimination), and the discounted visitation
`d(s₀, ·)` as the rows of `(1 - γ) (I - γ P^σ)⁻¹`. For several policies and mixtures the run checks
exactly:

* Bellman consistency `V s = ∑ a, σ(a | s) qValue V s a` (`stochValue_eq`);
* that Dirac policies have the deterministic values of `policyBellman` (`stochValue_ofDet`);
* that each visitation row is a probability vector with mass at least `1 - γ` at its start, and
  that `∑ s, d(s₀, s) f s = (1 - γ) V_f(s₀)` (`sum_visitation`, `one_sub_le_visitation_self`,
  `sum_visitation_mul`);
* the performance difference identity (`performance_difference`) for every ordered pair;
* the conservative policy iteration bound (`cpi_improvement`) for `α ∈ {1/10, 1/2, 1}`.

It throws otherwise. Closed checks instantiate the theorems over `ℝ`.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision.Simplex

private abbrev St := Fin 3
private abbrev Ac := Fin 2

private meta def machine : MDP St Ac ℚ where
  reward := ![![3, 1], ![2, 0], ![-1, -4]]
  prob := ![![![1/2, 1/2, 0], ![1, 0, 0]],
    ![![0, 1/2, 1/2], ![3/4, 1/4, 0]],
    ![![0, 0, 1], ![1/2, 1/2, 0]]]

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

private meta def kernel (σ : St → Ac → ℚ) (s s' : St) : ℚ :=
  sumA fun a => σ s a * machine.prob s a s'

private meta def rew (σ : St → Ac → ℚ) (s : St) : ℚ := sumA fun a => σ s a * machine.reward s a

private meta def value (σ : St → Ac → ℚ) : St → ℚ := solve (kernel σ) (rew σ)

/-- The discounted visitation `d(s₀, s) = (1 - γ) V_{1_s}(s₀)`. -/
private meta def visit (σ : St → Ac → ℚ) (s₀ s : St) : ℚ :=
  (1 - γm) * solve (kernel σ) (fun s' => if s' = s then 1 else 0) s₀

private meta def adv (σ : St → Ac → ℚ) (s : St) (a : Ac) : ℚ :=
  qValue machine γm (value σ) s a - value σ s

private meta def dirac (π : St → Ac) : St → Ac → ℚ := fun s a => if a = π s then 1 else 0

private meta def mixQ (α : ℚ) (σ ρ : St → Ac → ℚ) : St → Ac → ℚ :=
  fun s a => (1 - α) * σ s a + α * ρ s a

private meta def policies : List (St → Ac → ℚ) :=
  [dirac ![0, 0, 0], dirac ![0, 1, 1], dirac ![1, 0, 1],
    fun _ _ => 1 / 2, ![![1/3, 2/3], ![1/4, 3/4], ![1, 0]], ![![0, 1], ![5/6, 1/6], ![1/2, 1/2]]]

#eval do
  let mut checks := 0
  for σ in policies do
    let V := value σ
    for s in sts do
      unless V s == sumA fun a => σ s a * qValue machine γm V s a do
        throw (IO.userError s!"Bellman consistency fails at {s}")
      for s₀ in sts do
        unless 0 ≤ visit σ s₀ s do throw (IO.userError "negative visitation")
      checks := checks + 1
    for s₀ in sts do
      unless sumS (visit σ s₀) == 1 do throw (IO.userError "visitation row does not sum to 1")
      unless 1 - γm ≤ visit σ s₀ s₀ do throw (IO.userError "start mass below 1 - γ")
      let f : St → ℚ := ![2, -3, 5]
      unless sumS (fun s => visit σ s₀ s * f s) == (1 - γm) * solve (kernel σ) f s₀ do
        throw (IO.userError "occupancy average fails")
  -- Dirac policies have their deterministic values
  for π in [![0, 0, 0], ![0, 1, 1], ![1, 1, 0]] do
    let V := value (dirac π)
    unless sts.all fun s => policyBellman machine γm π V s == V s do
      throw (IO.userError "Dirac value is not the deterministic value")
  -- performance difference lemma, all ordered pairs
  for σ in policies do
    for ρ in policies do
      for s₀ in sts do
        let lhs := value ρ s₀ - value σ s₀
        let rhs := (1 - γm)⁻¹ * sumS fun s => visit ρ s₀ s * sumA fun a => ρ s a * adv σ s a
        unless lhs == rhs do throw (IO.userError "performance difference identity fails")
        checks := checks + 1
  -- conservative policy iteration bound
  for σ in policies do
    for (ρ : St → Ac → ℚ) in policies do
      let g : St → ℚ := fun s => sumA fun a => ρ s a * adv σ s a
      let ε := sts.foldl (fun m s => max m |g s|) 0
      for α in [1/10, 1/2, 1] do
        for s₀ in sts do
          let 𝔸 := sumS fun s => visit σ s₀ s * g s
          let gain := value (mixQ α σ ρ) s₀ - value σ s₀
          unless α / (1 - γm) * 𝔸 - 2 * α ^ 2 * γm * ε / (1 - γm) ^ 2 ≤ gain do
            throw (IO.userError "CPI improvement bound fails")
          checks := checks + 1
  IO.println s!"stochastic policies, PDL and CPI: {checks} exact checks passed"

/-! Closed checks over `ℝ` -/

example (M : MDP St Ac ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : St → Ac) :
    stochValue M γ hM hγ0 hγ1 (StochasticPolicy.ofDet π) = policyValue M γ hM hγ0 hγ1 π :=
  stochValue_ofDet hM hγ0 hγ1 π

example (M : MDP St Ac ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π π' : StochasticPolicy St Ac) (s₀ : St) :
    stochValue M γ hM hγ0 hγ1 π' s₀ - stochValue M γ hM hγ0 hγ1 π s₀ =
      (1 - γ)⁻¹ * ∑ s, occupancy hM hγ0 hγ1 π' s₀ s *
        ∑ a, π'.prob s a * advantage hM hγ0 hγ1 π s a :=
  performance_difference hM hγ0 hγ1 π π' s₀

#print axioms tendsto_mrpValue
#print axioms sum_visitation_mul
#print axioms stochValue_le_optimalValue
#print axioms performance_difference
#print axioms abs_sum_occupancy_mix_sub_le
#print axioms cpi_improvement

end Cslib.Algorithms.Lean.MarkovDecision.Simplex
