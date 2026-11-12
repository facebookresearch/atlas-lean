/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Stability of one-step methods

A one-step method for `x' = f(t, x)` on a grid `t₀ ≤ t₁ ≤ ⋯ ≤ t_J` computes
`x_{j+1} = x_j + h_j • Φ(t_j, x_j, h_j)` with step `h_j = t_{j+1} - t_j` and increment function
`Φ` (for explicit Euler, `Φ(t, x, h) = f(t, x)`). The method is *stable* on `[t₀, T]` if one
constant `S`, independent of the grid, bounds the gap between an exact run `x` and a perturbed
run `z_{j+1} = z_j + h_j • Φ(t_j, z_j, h_j) + δ_{j+1}`:
`‖x_j - z_j‖ ≤ S (‖x_0 - z_0‖ + ∑_{k=1}^J ‖δ_k‖)` for every `1 ≤ j ≤ J`.

## Main results

* `OneStepMethod.IsStable`: stability of an increment function on `[t₀, T]`.
* `OneStepMethod.norm_sub_le`: if `Φ` is `L`-Lipschitz in the state along the grid, then
  `‖x_j - z_j‖ ≤ e^{L (t_j - t_0)} ‖x_0 - z_0‖ + ∑_{k=1}^j e^{L (t_j - t_k)} ‖δ_k‖`.
* `OneStepMethod.isStable_of_lipschitz`: a method whose increment is `L`-Lipschitz in the state
  for all `t ∈ [t₀, T]` and `h ∈ (0, T - t₀]` is stable with `S = e^{L (T - t₀)}`.

## References

* S. Boisgérault, T. Romary, E. Chautru and P. Bernard, *Calcul Différentiel, Intégral et
  Stochastique* (Mines Paris), Équations Différentielles II, "Stabilité" and "Condition suffisante
  de stabilité".
* E. Hairer, S. P. Nørsett and G. Wanner, *Solving Ordinary Differential Equations I*, 2nd ed.,
  Section II.3.
-/

@[expose] public section

namespace MathlibExt.Analysis.ODE.OneStepMethod

open Finset Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The increment function `Φ` of a one-step method is *stable* on `[t₀, T]`: there is a constant
`S` such that, for every grid `t₀ = t 0 < t 1 < ⋯ < t J = T`, every run
`x (j + 1) = x j + h_j • Φ (t j) (x j) h_j` and every perturbed run
`z (j + 1) = z j + h_j • Φ (t j) (z j) h_j + δ (j + 1)` (with `h_j = t (j + 1) - t j`) satisfy
`‖x j - z j‖ ≤ S * (‖x 0 - z 0‖ + ∑ k ∈ Icc 1 J, ‖δ k‖)` for all `1 ≤ j ≤ J`. -/
def IsStable (Φ : ℝ → E → ℝ → E) (t₀ T : ℝ) : Prop :=
  ∃ S : ℝ, ∀ (J : ℕ) (t : ℕ → ℝ), t 0 = t₀ → t J = T → (∀ j < J, t j < t (j + 1)) →
    ∀ x z δ : ℕ → E,
      (∀ j < J, x (j + 1) = x j + (t (j + 1) - t j) • Φ (t j) (x j) (t (j + 1) - t j)) →
      (∀ j < J, z (j + 1) =
        z j + (t (j + 1) - t j) • Φ (t j) (z j) (t (j + 1) - t j) + δ (j + 1)) →
      ∀ j ∈ Icc 1 J, ‖x j - z j‖ ≤ S * (‖x 0 - z 0‖ + ∑ k ∈ Icc 1 J, ‖δ k‖)

/-- One step of the error recursion: `‖x_{j+1} - z_{j+1}‖ ≤ e^{L h_j} ‖x_j - z_j‖ + ‖δ_{j+1}‖`,
using `1 + L h ≤ e^{L h}`. -/
private lemma norm_sub_succ_le {Φ : ℝ → E → ℝ → E} {L s s' : ℝ} (hs : s ≤ s')
    {a b a' b' d : E}
    (hΦ : ‖Φ s a (s' - s) - Φ s b (s' - s)‖ ≤ L * ‖a - b‖)
    (ha : a' = a + (s' - s) • Φ s a (s' - s))
    (hb : b' = b + (s' - s) • Φ s b (s' - s) + d) :
    ‖a' - b'‖ ≤ exp (L * (s' - s)) * ‖a - b‖ + ‖d‖ := by
  have hh : 0 ≤ s' - s := sub_nonneg.2 hs
  have key : a' - b' = (a - b) + (s' - s) • (Φ s a (s' - s) - Φ s b (s' - s)) - d := by
    rw [ha, hb, smul_sub]; abel
  calc ‖a' - b'‖
      ≤ ‖a - b‖ + (s' - s) * ‖Φ s a (s' - s) - Φ s b (s' - s)‖ + ‖d‖ := by
        rw [key]
        calc ‖a - b + (s' - s) • (Φ s a (s' - s) - Φ s b (s' - s)) - d‖
            ≤ ‖a - b + (s' - s) • (Φ s a (s' - s) - Φ s b (s' - s))‖ + ‖d‖ := norm_sub_le _ _
          _ ≤ ‖a - b‖ + ‖(s' - s) • (Φ s a (s' - s) - Φ s b (s' - s))‖ + ‖d‖ := by
              gcongr; exact norm_add_le _ _
          _ = _ := by rw [norm_smul, Real.norm_of_nonneg hh]
    _ ≤ ‖a - b‖ + (s' - s) * (L * ‖a - b‖) + ‖d‖ := by gcongr
    _ = (1 + L * (s' - s)) * ‖a - b‖ + ‖d‖ := by ring
    _ ≤ exp (L * (s' - s)) * ‖a - b‖ + ‖d‖ := by
        gcongr
        linarith [add_one_le_exp (L * (s' - s))]

/-- If the increment `Φ` is `L`-Lipschitz in the state at every grid step, an exact run `x` and a
perturbed run `z` of the one-step method satisfy, for every `j ≤ J`,
`‖x j - z j‖ ≤ e^{L (t j - t 0)} ‖x 0 - z 0‖ + ∑ k ∈ Icc 1 j, e^{L (t j - t k)} ‖δ k‖`. -/
theorem norm_sub_le {Φ : ℝ → E → ℝ → E} {L : ℝ} {J : ℕ} {t : ℕ → ℝ}
    (ht : ∀ j < J, t j ≤ t (j + 1))
    (hΦ : ∀ j < J, ∀ a b : E,
      ‖Φ (t j) a (t (j + 1) - t j) - Φ (t j) b (t (j + 1) - t j)‖ ≤ L * ‖a - b‖)
    {x z δ : ℕ → E}
    (hx : ∀ j < J, x (j + 1) = x j + (t (j + 1) - t j) • Φ (t j) (x j) (t (j + 1) - t j))
    (hz : ∀ j < J, z (j + 1) =
      z j + (t (j + 1) - t j) • Φ (t j) (z j) (t (j + 1) - t j) + δ (j + 1)) :
    ∀ j ≤ J, ‖x j - z j‖ ≤
      exp (L * (t j - t 0)) * ‖x 0 - z 0‖ + ∑ k ∈ Icc 1 j, exp (L * (t j - t k)) * ‖δ k‖ := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have hjJ : j < J := hj
    have hstep := norm_sub_succ_le (ht j hjJ) (hΦ j hjJ _ _) (hx j hjJ) (hz j hjJ)
    calc ‖x (j + 1) - z (j + 1)‖
        ≤ exp (L * (t (j + 1) - t j)) * ‖x j - z j‖ + ‖δ (j + 1)‖ := hstep
      _ ≤ exp (L * (t (j + 1) - t j)) * (exp (L * (t j - t 0)) * ‖x 0 - z 0‖ +
            ∑ k ∈ Icc 1 j, exp (L * (t j - t k)) * ‖δ k‖) + ‖δ (j + 1)‖ := by
          gcongr
          exact ih hjJ.le
      _ = exp (L * (t (j + 1) - t 0)) * ‖x 0 - z 0‖ +
            ∑ k ∈ Icc 1 (j + 1), exp (L * (t (j + 1) - t k)) * ‖δ k‖ := by
          have e1 : ∀ (u c : ℝ), exp (L * (t (j + 1) - t j)) * (exp (L * (t j - u)) * c) =
              exp (L * (t (j + 1) - u)) * c := fun u c ↦ by
            rw [← mul_assoc, ← exp_add]; ring_nf
          rw [sum_Icc_succ_top (Nat.le_add_left 1 j), mul_add, mul_sum, e1]
          simp_rw [e1]
          simp only [sub_self, mul_zero, exp_zero, one_mul]
          ring

/-- **Sufficient condition for stability.** If the increment `Φ` is `L`-Lipschitz in the state,
uniformly for `t ∈ [t₀, T]` and step `h ∈ (0, T - t₀]`, the one-step method is stable on
`[t₀, T]` with constant `e^{L (T - t₀)}`. -/
theorem isStable_of_lipschitz {Φ : ℝ → E → ℝ → E} {L t₀ T : ℝ} (hL : 0 ≤ L)
    (hΦ : ∀ s ∈ Set.Icc t₀ T, ∀ h ∈ Set.Ioc 0 (T - t₀), ∀ a b : E,
      ‖Φ s a h - Φ s b h‖ ≤ L * ‖a - b‖) :
    IsStable Φ t₀ T := by
  refine ⟨exp (L * (T - t₀)), fun J t ht0 htJ ht' x z δ hx hz j hj' ↦ ?_⟩
  have ht : ∀ j < J, t j ≤ t (j + 1) := fun j hj ↦ (ht' j hj).le
  have hj : j ≤ J := (mem_Icc.1 hj').2
  -- The grid is increasing, so every node lies in `[t₀, T]` and every step in `(0, T - t₀]`.
  have hmono : ∀ i ≤ J, ∀ k ≤ i, t k ≤ t i := by
    intro i hi k hk
    induction i with
    | zero => rw [Nat.le_zero.1 hk]
    | succ i ih =>
      rcases Nat.of_le_succ hk with hk | rfl
      · exact (ih (Nat.le_of_succ_le hi) hk).trans (ht i hi)
      · exact le_rfl
  have hmem : ∀ i ≤ J, t i ∈ Set.Icc t₀ T := fun i hi ↦
    ⟨ht0 ▸ hmono i hi 0 (Nat.zero_le i), htJ ▸ hmono J le_rfl i hi⟩
  have hΦgrid : ∀ i < J, ∀ a b : E,
      ‖Φ (t i) a (t (i + 1) - t i) - Φ (t i) b (t (i + 1) - t i)‖ ≤ L * ‖a - b‖ := by
    intro i hi a b
    refine hΦ _ (hmem i hi.le) _ ⟨sub_pos.2 (ht' i hi), ?_⟩ a b
    have h1 := (hmem (i + 1) hi).2
    have h2 := (hmem i hi.le).1
    linarith
  have hbound := norm_sub_le ht hΦgrid hx hz j hj
  have hjT : t j - t 0 ≤ T - t₀ := by rw [ht0]; linarith [(hmem j hj).2]
  calc ‖x j - z j‖
      ≤ exp (L * (t j - t 0)) * ‖x 0 - z 0‖ + ∑ k ∈ Icc 1 j, exp (L * (t j - t k)) * ‖δ k‖ :=
        hbound
    _ ≤ exp (L * (T - t₀)) * ‖x 0 - z 0‖ + ∑ k ∈ Icc 1 J, exp (L * (T - t₀)) * ‖δ k‖ := by
        gcongr ?_ * _ + ?_
        · exact exp_le_exp.2 (mul_le_mul_of_nonneg_left hjT hL)
        · calc ∑ k ∈ Icc 1 j, exp (L * (t j - t k)) * ‖δ k‖
              ≤ ∑ k ∈ Icc 1 j, exp (L * (T - t₀)) * ‖δ k‖ := by
                refine sum_le_sum fun k hk ↦ ?_
                rw [mem_Icc] at hk
                have hk0 := (hmem k (hk.2.trans hj)).1
                have hjT' := (hmem j hj).2
                gcongr
            _ ≤ ∑ k ∈ Icc 1 J, exp (L * (T - t₀)) * ‖δ k‖ :=
                sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hj)
                  fun _ _ _ ↦ by positivity
    _ = exp (L * (T - t₀)) * (‖x 0 - z 0‖ + ∑ k ∈ Icc 1 J, ‖δ k‖) := by
        rw [mul_add, mul_sum]

end MathlibExt.Analysis.ODE.OneStepMethod
