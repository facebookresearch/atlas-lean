/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path

/-!
# The countable-state jump–hold chain

On a countable state space `S`, with rates `q : S → ℝ` and a jump kernel `P : S → PMF S`, this
file builds the continuous-time chain by the jump chain / holding time construction (Norris
1997, §2.6). The randomness is an i.i.d. sequence of steps `ω n = (ξ n, E n)` under
`inputMeasure P`, where `ξ n : S → S` has independent coordinates `ξ n x ∼ P x` and `E n` is an
independent `Exp(1)` clock. The jump chain is `Y 0 = x₀`, `Y (n + 1) = ξ n (Y n)`
(`ProbabilityTheory.ctmcJumpChain`, shared with the finite-state construction), the holding
times are `E n / q (Y n)` and the jump times are their partial sums.

## Main definitions

* `JumpHold.stepMeasure P`, `JumpHold.inputMeasure P`: the law of one step and of the i.i.d.
  step sequence.
* `JumpHold.holdingTime`, `JumpHold.jumpTime`: the holding times and the jump times.
* `JumpHold.stateAt`, `JumpHold.path`: the state at time `s` after `n` jumps, and the path.

## Main results

* `JumpHold.jumpTime_succ_eq`: first-step decomposition of the jump times.
* `JumpHold.path_eq_ctmcJumpChain`: with positive rates and nonnegative clocks, the path at a
  time `s` with `T k ≤ s < T (k + 1)` is the jump chain `Y k`.

## Implementation notes

These declarations keep their names in the namespace
`MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion.JumpHold` of the stochastic reaction
network development, which proves the Foster–Lyapunov non-explosion criterion and the
fixed-time moment bound for this chain, so that existing references stay valid.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §2.6–2.7.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory

namespace MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion

namespace JumpHold

variable {S : Type*}

section Measure

variable [MeasurableSpace S]

/-- The law of one step `(ξ, E)`: `ξ : S → S` has independent coordinates with `ξ x ∼ P x`, and
`E` is an independent exponential clock of rate `1`. -/
noncomputable def stepMeasure (P : S → PMF S) : Measure ((S → S) × ℝ) :=
  (Measure.infinitePi fun x => (P x).toMeasure).prod (expMeasure 1)

instance (P : S → PMF S) : IsProbabilityMeasure (stepMeasure P) := by
  have := isProbabilityMeasure_expMeasure (r := 1) one_pos
  unfold stepMeasure
  infer_instance

/-- The law of the i.i.d. step sequence `ω : ℕ → (S → S) × ℝ` driving the chain. -/
noncomputable def inputMeasure (P : S → PMF S) : Measure (ℕ → (S → S) × ℝ) :=
  Measure.infinitePi fun _ => stepMeasure P

instance (P : S → PMF S) : IsProbabilityMeasure (inputMeasure P) := by
  unfold inputMeasure
  infer_instance

end Measure

/-- The `n`-th holding time `E n / q (Y n)` of the chain started at `x`, meant for positive rates
`q` and nonnegative clocks. With the convention `a / 0 = 0` it is `0` when `q (Y n) = 0`. -/
noncomputable def holdingTime (q : S → ℝ) (x : S) (ω : ℕ → (S → S) × ℝ) (n : ℕ) : ℝ :=
  (ω n).2 / q (ctmcJumpChain x ω n)

/-- The `n`-th jump time `T n = H 0 + ⋯ + H (n - 1)` of the chain started at `x`, the sum of the
first `n` holding times `H k` (so `T 0 = 0`; with `a / 0 = 0`, a state with `q = 0` adds `0`). -/
noncomputable def jumpTime (q : S → ℝ) (x : S) (ω : ℕ → (S → S) × ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, holdingTime q x ω k

/-- The jump chain one step later is the jump chain of the shifted steps started at `ξ 0 x`. -/
theorem ctmcJumpChain_succ_eq (x : S) (ω : ℕ → (S → S) × ℝ) (j : ℕ) :
    ctmcJumpChain x ω (j + 1) = ctmcJumpChain ((ω 0).1 x) (ctmcShift 1 ω) j := by
  rw [show ((ω 0).1 x) = ctmcJumpChain x ω 1 from rfl, ctmcJumpChain_shift, Nat.add_comm]

/-- First-step decomposition of the jump times: `T (j + 1) = E 0 / q x + T' j`, where `T'` are
the jump times of the shifted steps started at `ξ 0 x`. With the convention `a / 0 = 0`,
`E 0 / q x = 0` when `q x = 0`. -/
theorem jumpTime_succ_eq (q : S → ℝ) (x : S) (ω : ℕ → (S → S) × ℝ) (j : ℕ) :
    jumpTime q x ω (j + 1) = (ω 0).2 / q x + jumpTime q ((ω 0).1 x) (ctmcShift 1 ω) j := by
  simp only [jumpTime, sum_range_succ', holdingTime, ctmcJumpChain_succ_eq]
  simp only [ctmcShift, Nat.add_comm 1, ctmcJumpChain, add_comm]

/-! ### The path -/

variable {q : S → ℝ}

/-- The state at time `s` of the chain started at `x` and stopped after `n` jumps, by recursion
on the first step. With the convention `a / 0 = 0`, a state with `q x = 0` is left at once at
every time `s ≥ 0`; for positive rates and nonnegative clocks, the state at a time `s < 0` is
`x`. -/
noncomputable def stateAt (q : S → ℝ) : ℕ → S → ℝ → (ℕ → (S → S) × ℝ) → S
  | 0, x, _, _ => x
  | n + 1, x, s, ω =>
    if s < (ω 0).2 / q x then x
    else stateAt q n ((ω 0).1 x) (s - (ω 0).2 / q x) (ctmcShift 1 ω)

/-- For `0 ≤ s < T m` and `m ≤ n`, running `n` instead of `m` jumps does not change the state at
time `s`. -/
theorem stateAt_eq_of_lt (m : ℕ) :
    ∀ (n : ℕ) (x : S) (s : ℝ) (ω : ℕ → (S → S) × ℝ), 0 ≤ s → s < jumpTime q x ω m → m ≤ n →
      stateAt q n x s ω = stateAt q m x s ω := by
  induction m with
  | zero => intro n x s ω hs hlt _; simp [jumpTime] at hlt; linarith
  | succ m ih =>
    intro n x s ω hs hlt hmn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [stateAt]
    split_ifs with h
    · rfl
    · rw [jumpTime_succ_eq] at hlt
      exact ih n _ _ _ (by linarith [not_lt.mp h]) (by linarith) (by omega)

/-- With positive rates and nonnegative clocks the jump times are nonnegative. -/
theorem jumpTime_nonneg (hq : ∀ x, 0 < q x) {ω : ℕ → (S → S) × ℝ} (hE : ∀ k, 0 ≤ (ω k).2)
    (x : S) (n : ℕ) : 0 ≤ jumpTime q x ω n :=
  sum_nonneg fun k _ => div_nonneg (hE k) (hq _).le

/-- With positive rates and nonnegative clocks, if `T k ≤ s < T (k + 1)` and `k < n`, then the
state at time `s` is `Y k`. -/
theorem stateAt_eq_ctmcJumpChain (hq : ∀ x, 0 < q x) (n : ℕ) :
    ∀ (x : S) (s : ℝ) (ω : ℕ → (S → S) × ℝ) (k : ℕ), (∀ j, 0 ≤ (ω j).2) → k < n →
      jumpTime q x ω k ≤ s → s < jumpTime q x ω (k + 1) →
      stateAt q n x s ω = ctmcJumpChain x ω k := by
  induction n with
  | zero => intro x s ω k _ hk; omega
  | succ n ih =>
    intro x s ω k hE hk h₁ h₂
    have hE' : ∀ j, 0 ≤ (ctmcShift 1 ω j).2 := fun j => hE (1 + j)
    simp only [stateAt]
    split_ifs with h
    · rcases k with _ | k
      · rfl
      · rw [jumpTime_succ_eq] at h₁
        linarith [jumpTime_nonneg hq hE' ((ω 0).1 x) k]
    · rcases k with _ | k
      · rw [show jumpTime q x ω (0 + 1) = (ω 0).2 / q x by
          simp [jumpTime, holdingTime, ctmcJumpChain]] at h₂
        exact absurd h₂ h
      · rw [jumpTime_succ_eq] at h₁ h₂
        rw [ih _ _ _ k hE' (by omega) (by linarith) (by linarith), ctmcJumpChain_succ_eq]

open scoped Classical in
/-- The **path** `X s` of the chain started at `x`: the state at time `s` after enough jumps.
If `s` is at or after the explosion time (a null event under the hypotheses of
`ae_tendsto_jumpTime_atTop`), the value is the junk state `x`. For `s < 0` it is `x` too, since
`T 0 = 0`. -/
noncomputable def path (q : S → ℝ) (x : S) (ω : ℕ → (S → S) × ℝ) (s : ℝ) : S :=
  if h : ∃ n, s < jumpTime q x ω n then stateAt q (Nat.find h) x s ω else x

/-- If `0 ≤ s < T n`, the path at time `s` is the state at time `s` after `n` jumps. -/
theorem stateAt_eq_path {n : ℕ} {x : S} {ω : ℕ → (S → S) × ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hn : s < jumpTime q x ω n) : stateAt q n x s ω = path q x ω s := by
  classical
  have h : ∃ n, s < jumpTime q x ω n := ⟨n, hn⟩
  simp only [path, h, ↓reduceDIte]
  exact stateAt_eq_of_lt _ n x s ω hs (Nat.find_spec h) (Nat.find_min' h hn)

/-- With positive rates and nonnegative clocks, `X s = Y k` for `T k ≤ s < T (k + 1)`. -/
theorem path_eq_ctmcJumpChain (hq : ∀ x, 0 < q x) {x : S} {ω : ℕ → (S → S) × ℝ}
    (hE : ∀ j, 0 ≤ (ω j).2) {s : ℝ} {k : ℕ} (h₁ : jumpTime q x ω k ≤ s)
    (h₂ : s < jumpTime q x ω (k + 1)) : path q x ω s = ctmcJumpChain x ω k := by
  rw [← stateAt_eq_path ((jumpTime_nonneg hq hE x k).trans h₁) h₂]
  exact stateAt_eq_ctmcJumpChain hq (k + 1) x s ω k hE (Nat.lt_succ_self k) h₁ h₂

end JumpHold

end MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion
