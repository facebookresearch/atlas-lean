/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Lotka–Volterra predator–prey model

Prey `x` and predators `y` evolve by

  `x' = α x - β x y`,   `y' = δ x y - γ y`,

with prey growth rate `α`, predation rate `β`, predator conversion rate `δ` and predator death
rate `γ` (all positive in the ecological model; the derivative identity below holds for all real
parameters). In the open positive quadrant the system has the first integral

  `V(x, y) = δ x - γ log x + β y - α log y`,

so positive solutions stay on level curves of `V`. For positive parameters `V` attains its
minimum at the coexistence equilibrium `(γ / δ, α / β)`, whose level set is the single point;
the other level sets are the closed orbits of the classical periodic oscillations.

## Main results

* `firstIntegral`: the function `V`.
* `hasDerivAt_firstIntegral`: `V` has zero time derivative along a solution at any time where
  both populations are positive.
* `firstIntegral_eq`: `V` is constant along a solution that stays positive on `[0, ∞)`.
* `firstIntegral_equilibrium_le`: `V(γ / δ, α / β) ≤ V(x, y)` for `x, y > 0`.

## References

* A. J. Lotka, *Elements of Physical Biology*, Williams & Wilkins (1925).
* V. Volterra, *Variazioni e fluttuazioni del numero d'individui in specie animali conviventi*,
  Mem. R. Accad. Naz. dei Lincei 2 (1926) 31–113.
* J. Hofbauer and K. Sigmund, *Evolutionary Games and Population Dynamics*, Cambridge
  University Press (1998), §2.2.
-/

@[expose] public section

open Real Set

namespace MathlibExt.Biology.Dynamics.LotkaVolterra

/-- The Lotka–Volterra first integral `V(x, y) = δ x - γ log x + β y - α log y` for the
system `x' = α x - β x y`, `y' = δ x y - γ y`. It is meaningful on the open positive quadrant
`x, y > 0`; elsewhere `Real.log` takes junk values (`log 0 = 0`, `log (-x) = log x`). -/
noncomputable def firstIntegral (α β γ δ x y : ℝ) : ℝ :=
  δ * x - γ * log x + β * y - α * log y

/-- **Lotka–Volterra first integral.** If `x' = α x - β x y` and `y' = δ x y - γ y` at time `t`
and `x t, y t > 0`, then `t ↦ V(x t, y t)` has derivative `0` at `t`. -/
theorem hasDerivAt_firstIntegral {α β γ δ : ℝ} {x y : ℝ → ℝ} {t : ℝ}
    (hx : HasDerivAt x (α * x t - β * x t * y t) t)
    (hy : HasDerivAt y (δ * x t * y t - γ * y t) t) (hx0 : 0 < x t) (hy0 : 0 < y t) :
    HasDerivAt (fun s => firstIntegral α β γ δ (x s) (y s)) 0 t := by
  have h := (((hx.const_mul δ).sub ((hx.log hx0.ne').const_mul γ)).add
    (hy.const_mul β)).sub ((hy.log hy0.ne').const_mul α)
  convert h using 1
  · funext s
    simp only [firstIntegral, Pi.sub_apply, Pi.add_apply]
  · rw [show (α * x t - β * x t * y t) / x t = α - β * y t by field_simp,
      show (δ * x t * y t - γ * y t) / y t = δ * x t - γ by field_simp]
    ring

/-- **Positive solutions lie on level curves.** If `(x, y)` solves the Lotka–Volterra system
on `[0, ∞)` and both populations stay positive there, then `V(x t, y t) = V(x 0, y 0)` for
all `t ≥ 0`. -/
theorem firstIntegral_eq {α β γ δ : ℝ} {x y : ℝ → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (α * x t - β * x t * y t) t)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (δ * x t * y t - γ * y t) t)
    (hx0 : ∀ t, 0 ≤ t → 0 < x t) (hy0 : ∀ t, 0 ≤ t → 0 < y t) {t : ℝ} (ht : 0 ≤ t) :
    firstIntegral α β γ δ (x t) (y t) = firstIntegral α β γ δ (x 0) (y 0) := by
  have hd : ∀ s, 0 ≤ s → HasDerivAt (fun s => firstIntegral α β γ δ (x s) (y s)) 0 s :=
    fun s hs => hasDerivAt_firstIntegral (hx s hs) (hy s hs) (hx0 s hs) (hy0 s hs)
  exact constant_of_has_deriv_right_zero (b := t)
    (fun s hs => (hd s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hd s hs.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩

/-- `a z - b log z` is minimized over `z > 0` at `z = b / a` (for `a, b > 0`). -/
private theorem mul_sub_mul_log_le {a b z : ℝ} (ha : 0 < a) (hb : 0 < b) (hz : 0 < z) :
    a * (b / a) - b * log (b / a) ≤ a * z - b * log z := by
  have hq : 0 < a * z / b := by positivity
  have hlog := log_le_sub_one_of_pos hq
  rw [log_div (by positivity) hb.ne', log_mul ha.ne' hz.ne'] at hlog
  rw [log_div hb.ne' ha.ne', mul_div_cancel₀ _ ha.ne']
  have : b * (log a + log z - log b) ≤ b * (a * z / b - 1) :=
    mul_le_mul_of_nonneg_left hlog hb.le
  rw [mul_sub b (a * z / b), mul_div_cancel₀ _ hb.ne'] at this
  linarith

/-- **The coexistence equilibrium minimizes the first integral.** For positive parameters and
`x, y > 0`, `V(γ / δ, α / β) ≤ V(x, y)`. -/
theorem firstIntegral_equilibrium_le {α β γ δ x y : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hδ : 0 < δ) (hx : 0 < x) (hy : 0 < y) :
    firstIntegral α β γ δ (γ / δ) (α / β) ≤ firstIntegral α β γ δ x y := by
  have h1 := mul_sub_mul_log_le hδ hγ hx
  have h2 := mul_sub_mul_log_le hβ hα hy
  unfold firstIntegral
  linarith

end MathlibExt.Biology.Dynamics.LotkaVolterra
