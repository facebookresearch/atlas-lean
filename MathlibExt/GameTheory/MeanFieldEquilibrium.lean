/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Mean field equilibria on a finite state space and Lasry–Lions uniqueness

A *mean field equilibrium* of a one-shot game with a continuum of identical players, each paying
`F(y, m)` for choosing the state `y` when the population distribution is `m`, is a distribution
`m̄` such that `∫ F(y, m̄) dm̄(y) = inf_m ∫ F(y, m̄) dm(y)`: no player gains by deviating, given the
crowd. Here the state space `Q` is finite, distributions are probability vectors `m : Q → ℝ`
(the weights of a point of Mathlib's `Convexity.StdSimplex ℝ Q`, see `weights_isProb`), and
the cost is a function `F : (Q → ℝ) → Q → ℝ`, `F m y` being the cost of state `y` against `m`.

## Main definitions

* `IsMeanFieldEquilibrium F m`: `m` is a probability vector (nonnegative, summing to `1`) and
  `∑ y, F m y * m y ≤ ∑ y, F m y * m' y` for every distribution `m'`.

## Main results

* `isMeanFieldEquilibrium_iff`: an equilibrium is exactly a distribution supported on the set of
  minimisers of `F m` (Cardaliaguet, Remark 2.5).
* `eq_of_isMeanFieldEquilibrium`: under the Lasry–Lions strict monotonicity condition
  `∑ y, (F m₁ y - F m₂ y) * (m₁ y - m₂ y) > 0` for distinct distributions, there is at most one
  equilibrium (Cardaliaguet, Proposition 2.9).
* `lasryLions_identity`: the pointwise identity behind the Lasry–Lions uniqueness proof for the
  mean field game system (Cardaliaguet, proof of Theorem 3.6).

## References

* P. Cardaliaguet, *Notes on Mean Field Games (from P.-L. Lions' lectures at Collège de France)*,
  version of 27 September 2013, §2.2–2.4 (equation (4), Remark 2.5, Proposition 2.9) and §3.3
  (Theorem 3.6).
* J.-M. Lasry and P.-L. Lions, *Mean field games*, Japan. J. Math. 2 (2007) 229–260.
-/

@[expose] public section

namespace MathlibExt.GameTheory.MeanFieldEquilibrium

open Finset

variable {Q : Type*} [Fintype Q]

/-- **Mean field equilibrium on a finite state space** (Lasry–Lions; Cardaliaguet, *Notes on
Mean Field Games*, 2013, equation (4) with `Q` finite). Given the cost `F m y` of the state `y`
when the population is distributed according to `m`, a distribution `m` (a probability vector)
is a mean field equilibrium if `∑ y, F m y * m y ≤ ∑ y, F m y * m' y` for every
probability vector `m'`, i.e. `∫ F(y, m) dm(y) = inf_{m'} ∫ F(y, m) dm'(y)`. The values of `F`
at vectors that are not probability vectors play no role. -/
def IsMeanFieldEquilibrium (F : (Q → ℝ) → Q → ℝ) (m : Q → ℝ) : Prop :=
  ((∀ y, 0 ≤ m y) ∧ ∑ y, m y = 1) ∧
    ∀ m' : Q → ℝ, ((∀ y, 0 ≤ m' y) ∧ ∑ y, m' y = 1) → ∑ y, F m y * m y ≤ ∑ y, F m y * m' y

variable {F : (Q → ℝ) → Q → ℝ} {m : Q → ℝ}

/-- **Points of the standard simplex are probability vectors.** The weights of a point of
`Convexity.StdSimplex ℝ Q` are nonnegative and sum to `1`, the form of distribution used by
`IsMeanFieldEquilibrium`; this bridges to the mixed strategies of Nash's theorem. -/
theorem weights_isProb (σ : Convexity.StdSimplex ℝ Q) :
    (∀ y, 0 ≤ σ.weights y) ∧ ∑ y, σ.weights y = 1 :=
  ⟨fun y => σ.nonneg y, by
    have h := σ.total
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h⟩

/-- **Equilibria are supported on minimisers** (Cardaliaguet, *Notes on Mean Field Games*,
Remark 2.5, `Q` finite). A distribution `m` is a mean field equilibrium if and only if every
state charged by `m` minimises the cost `F m`: `m x ≠ 0 → F m x ≤ F m y` for all `y`. -/
theorem isMeanFieldEquilibrium_iff :
    IsMeanFieldEquilibrium F m ↔ ((∀ y, 0 ≤ m y) ∧ ∑ y, m y = 1) ∧
      ∀ x, m x ≠ 0 → ∀ y, F m x ≤ F m y := by
  classical
  constructor
  · rintro ⟨hm, hle⟩
    refine ⟨hm, fun x hx y => ?_⟩
    by_contra hlt
    push Not at hlt
    have hxy : x ≠ y := by rintro rfl; exact lt_irrefl _ hlt
    have hmx : 0 < m x := lt_of_le_of_ne (hm.1 x) (Ne.symm hx)
    -- move the mass of `x` to `y`
    set m' : Q → ℝ := fun z =>
      m z + m x * ((Pi.single y (1 : ℝ) : Q → ℝ) z - (Pi.single x (1 : ℝ) : Q → ℝ) z) with hm'
    have hm'mem : ((∀ y, 0 ≤ m' y) ∧ ∑ y, m' y = 1) := by
      refine ⟨fun z => ?_, ?_⟩
      · by_cases hzx : z = x
        · subst hzx; simp [hm', Pi.single_apply, hxy]
        · by_cases hzy : z = y
          · subst hzy; simp [hm', Pi.single_apply, hzx]; nlinarith [hm.1 z]
          · simp [hm', Pi.single_apply, hzx, hzy, hm.1 z]
      · simp only [hm', sum_add_distrib, ← mul_sum, sum_sub_distrib]
        simp [hm.2]
    have h := hle m' hm'mem
    have hexp : ∑ z, F m z * m' z = ∑ z, F m z * m z + m x * (F m y - F m x) := by
      simp only [hm', mul_add, sum_add_distrib, mul_sub, sum_sub_distrib]
      simp [Pi.single_apply, mul_comm]
    rw [hexp] at h
    nlinarith
  · rintro ⟨hm, hmin⟩
    refine ⟨hm, fun m' hm' => ?_⟩
    have key : ∑ y, ∑ z, F m y * m y * m' z ≤ ∑ y, ∑ z, F m z * m y * m' z := by
      refine sum_le_sum fun y _ => sum_le_sum fun z _ => ?_
      by_cases hy : m y = 0
      · simp [hy]
      · have := hmin y hy z
        have h0 : 0 ≤ m y * m' z := mul_nonneg (hm.1 y) (hm'.1 z)
        nlinarith
    have lhs : ∑ y, ∑ z, F m y * m y * m' z = ∑ y, F m y * m y := by
      simp [← mul_sum, hm'.2]
    have rhs : ∑ y, ∑ z, F m z * m y * m' z = ∑ z, F m z * m' z := by
      rw [sum_comm]
      refine sum_congr rfl fun z _ => ?_
      have : ∑ y, F m z * m y * m' z = F m z * m' z * ∑ y, m y := by
        rw [mul_sum]; refine sum_congr rfl fun y _ => by ring
      rw [this, hm.2, mul_one]
    linarith

/-- **Lasry–Lions uniqueness of mean field equilibria** (Lasry–Lions; Cardaliaguet, *Notes on
Mean Field Games*, Proposition 2.9 and condition (7), `Q` finite). If the cost is strictly
monotone, `∑ y, (F m₁ y - F m₂ y) * (m₁ y - m₂ y) > 0` for distinct distributions `m₁ ≠ m₂`,
then there is at most one mean field equilibrium. Proof: add the two equilibrium inequalities
`∫ F(m₁) d(m₁ - m₂) ≤ 0` and `∫ F(m₂) d(m₂ - m₁) ≤ 0`. -/
theorem eq_of_isMeanFieldEquilibrium
    (hmono : ∀ m₁ m₂ : Q → ℝ, ((∀ y, 0 ≤ m₁ y) ∧ ∑ y, m₁ y = 1) →
      ((∀ y, 0 ≤ m₂ y) ∧ ∑ y, m₂ y = 1) → m₁ ≠ m₂ →
      0 < ∑ y, (F m₁ y - F m₂ y) * (m₁ y - m₂ y))
    {m₁ m₂ : Q → ℝ} (h₁ : IsMeanFieldEquilibrium F m₁) (h₂ : IsMeanFieldEquilibrium F m₂) :
    m₁ = m₂ := by
  by_contra hne
  have hpos := hmono m₁ m₂ h₁.1 h₂.1 hne
  have e₁ := h₁.2 m₂ h₂.1
  have e₂ := h₂.2 m₁ h₁.1
  have hsplit : ∑ y, (F m₁ y - F m₂ y) * (m₁ y - m₂ y) =
      (∑ y, F m₁ y * m₁ y - ∑ y, F m₁ y * m₂ y) - (∑ y, F m₂ y * m₁ y - ∑ y, F m₂ y * m₂ y) := by
    simp only [sub_mul, mul_sub, sum_sub_distrib]
    ring
  linarith

/-- **The Lasry–Lions identity** (Cardaliaguet, *Notes on Mean Field Games*, proof of
Theorem 3.6). For densities `m₁, m₂` and gradients `a = Du₁`, `b = Du₂` in a real inner product
space,
`(m₁ - m₂)/2 (‖a‖² - ‖b‖²) - ⟪a - b, m₁ a - m₂ b⟫ = -((m₁ + m₂)/2) ‖a - b‖²`.
Integrated over space and time it turns the duality between the Hamilton–Jacobi–Bellman and
Fokker–Planck equations of the mean field game system into
`∫∫ (m₁ - m₂)(F(x, m₁) - F(x, m₂)) ≤ 0`, which the monotonicity condition makes impossible unless
`m₁ = m₂`. -/
theorem lasryLions_identity {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (m₁ m₂ : ℝ) (a b : V) :
    (m₁ - m₂) / 2 * (‖a‖ ^ 2 - ‖b‖ ^ 2) - inner ℝ (a - b) (m₁ • a - m₂ • b) =
      -((m₁ + m₂) / 2) * ‖a - b‖ ^ 2 := by
  rw [@norm_sub_sq_real V, inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_comm b a]
  ring

end MathlibExt.GameTheory.MeanFieldEquilibrium
