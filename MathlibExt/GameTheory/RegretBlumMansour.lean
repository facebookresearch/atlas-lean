/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.Regret
import MathlibExt.Probability.FiniteMarkovChainConvergence

set_option autoImplicit false

@[expose] public section

/-!
# Blum-Mansour swap-regret decomposition

For a stationary master play, the master's swap regret is bounded by the
sum of the per-action copies' external regrets against their scaled loss
sequences. The module also proves that a stationary master play exists
whenever every copy plays a distribution at every time.

## References

* A. Blum and Y. Mansour, "From external to internal regret", *Journal of
  Machine Learning Research* 8 (2007), 1307-1324.
* T. Roughgarden, CS364A Lecture 18, "From External Regret to Swap Regret
  and the Minimax Theorem" (Stanford, 2013), Theorem 2.1.
-/

namespace MathlibExt.GameTheory.Regret

open scoped BigOperators

variable {K : Type*} [Fintype K] [DecidableEq K] [Nonempty K]
variable {T : ℕ}

/-- The losses fed to copy `j` in the Blum–Mansour reduction: `p t j * loss t a` at time `t`
and action `a`, for arbitrary real arrays `p` and `loss`. When each `p t` is a probability
distribution, these are the true losses scaled by the master's probability of `j` at time `t`. -/
def scaledLoss (p : Fin T → K → ℝ) (loss : Fin T → K → ℝ) (j : K) :
    Fin T → K → ℝ :=
  fun t a => p t j * loss t a

/-- The master play `p` is stationary for the copies' recommendations
`q` (`q t j` is copy `j`'s distribution at time `t`): at every time, `p t`
is a stationary distribution of the chain with transition probabilities
`q t j i` from `j` to `i`. -/
def IsStationaryPlay (q : Fin T → K → K → ℝ) (p : Fin T → K → ℝ) : Prop :=
  (∀ t j, IsSimplex (q t j)) ∧ (∀ t, IsSimplex (p t)) ∧
    ∀ t i, p t i = ∑ j, p t j * q t j i

omit [DecidableEq K] [Nonempty K] in
/-- Under stationarity, the master's expected loss is the sum over the
copies of their expected losses against their scaled loss sequences
(the equality of (2) and the left side of (6) in the lecture proof). -/
theorem expectedLoss_eq_sum_scaled (q : Fin T → K → K → ℝ)
    (p loss : Fin T → K → ℝ) (hp : IsStationaryPlay q p) :
    expectedLoss p loss =
      ∑ j, expectedLoss (fun t => q t j) (scaledLoss p loss j) := by
  obtain ⟨-, -, hstat⟩ := hp
  have h : ∀ (t : Fin T) (a : K),
      p t a * loss t a = ∑ j, q t j a * (p t j * loss t a) := by
    intro t a
    rw [hstat t a, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [expectedLoss, scaledLoss]
  calc (∑ t, ∑ a, p t a * loss t a)
      = ∑ t, ∑ a, ∑ j, q t j a * (p t j * loss t a) :=
        Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun a _ => h t a
    _ = ∑ t, ∑ j, ∑ a, q t j a * (p t j * loss t a) :=
        Finset.sum_congr rfl fun t _ => Finset.sum_comm
    _ = ∑ j, ∑ t, ∑ a, q t j a * (p t j * loss t a) := Finset.sum_comm

/-- **Blum–Mansour decomposition.** The master's swap regret is at most
the sum of the copies' external regrets against their scaled losses. -/
theorem swapRegret_le_sum_externalRegret_scaled (q : Fin T → K → K → ℝ)
    (p loss : Fin T → K → ℝ) (hp : IsStationaryPlay q p) :
    swapRegret p loss ≤
      ∑ j, externalRegret (fun t => q t j) (scaledLoss p loss j) := by
  have hC2 := expectedLoss_eq_sum_scaled q p loss hp
  simp only [swapRegret, externalRegret, expectedLoss, scaledLoss,
    cumulativeLoss] at hC2 ⊢
  obtain ⟨δstar, -, hδstar⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun δ : K → K => ∑ t, ∑ a, p t a * loss t (δ a))
  have hmain : ∑ j, Finset.univ.inf' Finset.univ_nonempty
        (fun a => ∑ t, p t j * loss t a)
      ≤ ∑ t, ∑ a, p t a * loss t (δstar a) := by
    calc ∑ j, Finset.univ.inf' Finset.univ_nonempty
            (fun a => ∑ t, p t j * loss t a)
        ≤ ∑ j, ∑ t, p t j * loss t (δstar j) :=
          Finset.sum_le_sum fun j _ => Finset.inf'_le _ (Finset.mem_univ _)
      _ = ∑ t, ∑ a, p t a * loss t (δstar a) := Finset.sum_comm
  simp only [hδstar, hC2, Finset.sum_sub_distrib]
  exact sub_le_sub_left hmain _

omit [DecidableEq K] in
/-- **Existence of a stationary play.** If every copy plays a distribution
at every time, some master play is stationary for the copies'
recommendations. -/
theorem exists_isStationaryPlay (q : Fin T → K → K → ℝ)
    (hq : ∀ t j, IsSimplex (q t j)) :
    ∃ p : Fin T → K → ℝ, IsStationaryPlay q p := by
  classical
  have hstat : ∀ t, ∃ π : K → ℝ, IsSimplex π ∧
      Matrix.vecMul π (Matrix.of (fun j i => q t j i)) = π := by
    intro t
    have hP : Matrix.of (fun j i => q t j i) ∈ Matrix.rowStochastic ℝ K := by
      rw [Matrix.mem_rowStochastic_iff_sum]
      constructor
      · intro i j
        simp only [Matrix.of_apply]
        obtain ⟨hpos, -⟩ := (isSimplex_iff _).mp (hq t i)
        exact hpos j
      · intro i
        simp only [Matrix.of_apply]
        obtain ⟨-, hsum⟩ := (isSimplex_iff _).mp (hq t i)
        exact hsum
    obtain ⟨π, hnonneg, hsum, hvec⟩ :=
      MathlibExt.Probability.FiniteMarkovChainConvergence.exists_stationary hP
    exact ⟨π, (isSimplex_iff π).mpr ⟨hnonneg, hsum⟩, hvec⟩
  choose p hp using hstat
  refine ⟨p, hq, ?_, ?_⟩
  · intro t
    exact (hp t).1
  · intro t i
    have hvec := (hp t).2
    have hi := congrFun hvec i
    simp only [Matrix.vecMul_apply, dotProduct, Matrix.col_apply,
      Matrix.of_apply] at hi
    exact hi.symm

end MathlibExt.GameTheory.Regret
