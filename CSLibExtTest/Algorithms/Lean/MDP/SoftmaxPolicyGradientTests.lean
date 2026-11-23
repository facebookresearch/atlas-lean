/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.SoftmaxPolicyGradient
public meta import CSLibExt.Algorithms.Lean.MDP.SoftmaxPolicyGradient

/-!
# Softmax policy gradient tests

A floating-point check of the policy gradient theorem for softmax policies
(`hasDerivAt_softmaxObjective`) on the maintenance MDP of the value-iteration tests, with rewards
rescaled to `[0, 1]` (`(r + 4) / 7`) and `γ = 9/10`. Policies are evaluated by Gauss-Jordan
elimination, and the discounted occupancy `d^π_{s₀}(s)` is `(1 - γ)` times the entry `(s₀, s)` of
`(I - γ P^π)⁻¹`. For three logit tables `θ` (zero, moderate and large entries) and three weight
vectors `μ` (uniform, a point mass and a vector with a negative entry, which is not a
distribution), the run compares, in every coordinate `θ(s, a)`, the central difference quotient
`(V^{π_{θ + h e}}(μ) - V^{π_{θ - h e}}(μ)) / (2 h)` with `h = 10⁻⁴` to the closed form
`(1 - γ)⁻¹ d^{π_θ}_μ(s) π_θ(a | s) A^{π_θ}(s, a)` (`softmaxPolicyGradient`), up to `10⁻⁶`, and
checks that the closed form sums to zero over the actions of each state. It throws otherwise. This
is a numerical diagnostic: the theorem itself is proved over `ℝ`. Closed checks instantiate the
theorem, including the edge case of a single action, where the gradient vanishes.
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

private meta def kernelF (θ : Array (Array Float)) (s s' : Nat) : Float :=
  sumN nA fun a => softmaxF θ s a * probF s a s'

private meta def valueF (θ : Array (Array Float)) : Array Float :=
  solveF (kernelF θ) (fun s => sumN nA fun a => softmaxF θ s a * rewardF s a)

/-- The objective `V^{π_θ}(μ) = ∑ s₀, μ s₀ V^{π_θ}(s₀)`. -/
private meta def objectiveF (μ : Array Float) (θ : Array (Array Float)) : Float :=
  let V := valueF θ
  sumN nS fun s₀ => μ.getD s₀ 0 * V.getD s₀ 0

/-- The discounted occupancy `d^π_μ(s) = ∑ s₀, μ s₀ (1 - γ) (I - γ P^π)⁻¹ (s₀, s)`. -/
private meta def occupancyF (μ : Array Float) (θ : Array (Array Float)) (s : Nat) : Float :=
  let col := solveF (kernelF θ) (fun s' => if s' = s then 1 else 0)
  sumN nS fun s₀ => μ.getD s₀ 0 * ((1 - γf) * col.getD s₀ 0)

/-- The closed form `(1 - γ)⁻¹ d^{π_θ}_μ(s) π_θ(a | s) A^{π_θ}(s, a)`. -/
private meta def gradientF (μ : Array Float) (θ : Array (Array Float)) (s a : Nat) : Float :=
  let V := valueF θ
  let q := rewardF s a + γf * sumN nS fun s' => probF s a s' * V.getD s' 0
  occupancyF μ θ s * softmaxF θ s a * (q - V.getD s 0) / (1 - γf)

/-- The logits `θ` with `θ(s, a)` shifted by `δ`. -/
private meta def shiftF (θ : Array (Array Float)) (s a : Nat) (δ : Float) : Array (Array Float) :=
  θ.set! s ((θ.getD s #[]).set! a ((θ.getD s #[]).getD a 0 + δ))

#eval do
  let h : Float := 1e-4
  let mut checks := 0
  for θ in [#[#[0, 0], #[0, 0], #[0, 0]], #[#[0.3, -1.2], #[2, 0.5], #[-0.7, 1.1]],
      #[#[4, -3], #[-5, 2.5], #[3, 6]]] do
    for μ in [#[1 / 3, 1 / 3, 1 / 3], #[1, 0, 0], #[0.5, -1, 2]] do
      for s in List.range nS do
        unless (sumN nA fun a => gradientF μ θ s a).abs ≤ 1e-9 do
          throw (IO.userError s!"θ = {θ}, μ = {μ}: the gradient at {s} does not sum to zero")
        for a in List.range nA do
          let fd := (objectiveF μ (shiftF θ s a h) - objectiveF μ (shiftF θ s a (-h))) / (2 * h)
          unless (fd - gradientF μ θ s a).abs ≤ 1e-6 do
            throw (IO.userError s!"θ = {θ}, μ = {μ}, (s, a) = ({s}, {a}): difference quotient \
              {fd} but closed form {gradientF μ θ s a}")
          checks := checks + 1
  IO.println s!"softmax policy gradient: {checks} floating-point checks passed"

/-! Closed checks over `ℝ` -/

/-- The theorem computes the partial derivative of the objective. -/
example {M : MDP (Fin 3) (Fin 2) ℝ} {γ : ℝ} (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (μ : Fin 3 → ℝ) (θ : Fin 3 → Fin 2 → ℝ) :
    deriv (fun x => softmaxObjective hM hγ0 hγ1 μ
        (Function.update θ 1 (Function.update (θ 1) 0 x))) (θ 1 0) =
      softmaxPolicyGradient hM hγ0 hγ1 μ θ 1 0 :=
  (hasDerivAt_softmaxObjective hM hγ0 hγ1 μ θ 1 0).deriv

/-- The gradient sums to zero over the actions of a state: shifting all logits of a state by the
same amount leaves the softmax policy unchanged. -/
example {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] {M : MDP S A ℝ}
    {γ : ℝ} (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : S → ℝ) (θ : S → A → ℝ)
    (s : S) : ∑ a, softmaxPolicyGradient hM hγ0 hγ1 μ θ s a = 0 := by
  have h := sum_prob_mul_advantage hM hγ0 hγ1 (StochasticPolicy.softmax θ) s
  simp only [softmaxPolicyGradient, mul_assoc, ← Finset.mul_sum, h, mul_zero]

/-- Edge case: with a single action the objective does not depend on the logits, and the
derivative is zero. -/
example {S : Type} [Fintype S] [DecidableEq S] {M : MDP S Unit ℝ} {γ : ℝ} (hM : M.Stochastic)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : S → ℝ) (θ : S → Unit → ℝ) (s : S) :
    HasDerivAt (fun x => softmaxObjective hM hγ0 hγ1 μ
      (Function.update θ s (Function.update (θ s) () x))) 0 (θ s ()) := by
  have h := sum_prob_mul_advantage hM hγ0 hγ1 (StochasticPolicy.softmax θ) s
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  have h0 : softmaxPolicyGradient hM hγ0 hγ1 μ θ s () = 0 := by
    simp only [softmaxPolicyGradient, mul_assoc, PUnit.default_eq_unit ▸ h, mul_zero]
  simpa only [h0] using hasDerivAt_softmaxObjective hM hγ0 hγ1 μ θ s ()

#print axioms hasDerivAt_softmaxObjective

end Cslib.Algorithms.Lean.MarkovDecision.Simplex
