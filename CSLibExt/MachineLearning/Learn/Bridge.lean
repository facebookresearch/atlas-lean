/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Hedge
public import CSLibExt.MachineLearning.Perceptron
public import CSLibExt.MachineLearning.AdaBoost

@[expose] public section

set_option autoImplicit false

namespace CSLibExt.MachineLearning.Learn

/-!
# LEARN bridge (Weeks 3-4 core, 90-day plan #4 LEARN)

One stable API for the three proved bounds the learning-theory work
builds on. Later LEARN files import this bridge, not the three files
directly, so if a bound moves (for example upstream to CSLib), only
this file changes.

The three bounds are the originals, restated with no change of
meaning. Do NOT redefine Hedge / AdaBoost / Perceptron here; the
Day-1 audit found all three already exist with proofs, and redefining
them would create the duplicates this bridge exists to prevent.

* `hedge_loss_bound`: Hedge (multiplicative weights) loss bound.
* `perceptron_mistake_bound`: Novikoff's mistake bound.
* `adaboost_error_bound`: AdaBoost training error decays exponentially
  in the number of rounds at fixed edge `γ`.

Next: Sauer-Shelah (growth function of a VC class) and Rademacher
uniform convergence, on top of the VC dimension CSLib already has.
-/

/-- Hedge loss bound: `(1 - exp (-η)) L ≤ η L_i + log n` for every
expert `i`. -/
theorem hedge_loss_bound {n : ℕ} {η : ℝ} (ls : List (Fin n → ℝ))
    (hb : Cslib.MachineLearning.Hedge.Bounded ls) (i : Fin n) :
    (1 - Real.exp (-η)) *
        Cslib.MachineLearning.Hedge.algLoss η ls (fun _ => 1) ≤
      η * Cslib.MachineLearning.Hedge.expertLoss i ls + Real.log n :=
  Cslib.MachineLearning.Hedge.algLoss_le ls hb i

/-- Novikoff's perceptron mistake bound: `k * γ ^ 2 ≤ (u ⬝ᵥ u) * R ^ 2`
for `k` mistakes against a `γ`-margin separator `u` with `x ⬝ᵥ x ≤ R ^ 2`. -/
theorem perceptron_mistake_bound {ι K : Type*} [Fintype ι] [CommRing K]
    [LinearOrder K] [IsStrictOrderedRing K] {u : ι → K} {γ R : K}
    (xs : List ((ι → K) × Bool))
    (hsep : ∀ e ∈ xs,
      γ ≤ Cslib.MachineLearning.Perceptron.sign e.2 *
        Matrix.dotProduct u e.1)
    (hR : ∀ e ∈ xs, Matrix.dotProduct e.1 e.1 ≤ R ^ 2) (hγ : 0 < γ) :
    ((Cslib.MachineLearning.Perceptron.run 0 0 xs).2 : K) * γ ^ 2 ≤
      Matrix.dotProduct u u * R ^ 2 :=
  Cslib.MachineLearning.Perceptron.mistakes_mul_sq_le xs hsep hR hγ

/-- AdaBoost training error: at most `exp (-2 γ² T)` after `T` rounds
with edge `γ`. -/
theorem adaboost_error_bound {m : ℕ} (hm : 0 < m) {γ : ℝ} (hγ : 0 ≤ γ)
    {y : Fin m → Bool} {wl : (Fin m → ℝ) → Fin m → Bool}
    (hwl : Cslib.MachineLearning.AdaBoost.WeakLearner y wl γ) (T : ℕ) :
    Cslib.MachineLearning.AdaBoost.trainErr y wl T ≤
      Real.exp (-2 * γ ^ 2 * T) :=
  Cslib.MachineLearning.AdaBoost.trainErr_le_exp hm hγ hwl T

end CSLibExt.MachineLearning.Learn
