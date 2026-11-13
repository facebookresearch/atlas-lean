/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Epidemiology.SIS
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Global stability of the SIS endemic equilibrium via a Lyapunov function

For the closed-population SIS model `MathlibExt.Biology.Epidemiology.SIS.IsSolution`,

  `S' = -β S I / N + γ I`,   `I' = β S I / N - γ I`,

with `N > 0` the (conserved) population size, the state space is the open segment
`{S + I = N, S > 0, I > 0}` of the positive orthant. When `R₀ = β / γ > 1` (and `γ > 0`) the
endemic equilibrium is `(S*, I*) = (N γ / β, N (1 - γ / β))`, which lies in that segment.

We prove that it is **globally asymptotically stable** on the segment using the Goh–Volterra
Lyapunov function

  `V(S, I) = (S - S* - S* log (S / S*)) + (I - I* - I* log (I / I*))`.

Along every solution with `S + I = N`, `S, I > 0`,

  `d/dt V(S, I) = -β (S - S*)² / S ≤ 0`,

with equality exactly at the equilibrium. The convergence argument is quantitative rather than
an appeal to LaSalle's principle:

1. `V` is nonincreasing, so `V(t) ≤ V(0)`; since `V ≥ I - I* - I* log (I / I*)`, this keeps
   `I(t) ≥ m := I* exp (-(V(0) + I*) / I*) > 0` (uniform persistence).
2. The elementary bound `x - a - a log (x / a) ≤ (x - a)² / x` gives
   `V ≤ (S - S*)² N / (S I)`, hence `V' ≤ -(β m / N) V`, and `V(t) ≤ V(0) e^{-c t}`.
3. The bound `(x - a)² ≤ 2 M (x - a - a log (x / a))` for `0 < x, a ≤ M` gives
   `(I - I*)² ≤ 2 N V`, so `I(t) → I*`, `S(t) = N - I(t) → S*`; combined with
   `V(0) ≤ (I(0) - I*)² N / (S(0) I(0))` it also gives Lyapunov stability.

Forward invariance of the open segment (`IsSolution.pos_of_pos`) is taken from the explicit
solution of `SIS.lean` (`IsSolution.infected_eq_sisInfected`); everything after it uses only the
Lyapunov function.

## Main results

* `lyapunov β γ N S I`: the Goh–Volterra function.
* `lyapunov_nonneg`, `lyapunov_eq_zero_iff`: `V ≥ 0` on the positive orthant, `= 0` only at
  `(S*, I*)`.
* `IsSolution.hasDerivAt_lyapunov`: `d/dt V = -β (S - S*)² / S` along solutions.
* `lyapunovDeriv_nonpos`, `lyapunovDeriv_eq_zero_iff`: the derivative is `≤ 0` and vanishes on
  the segment only at the equilibrium.
* `IsSolution.pos_of_pos`: forward invariance of `{S + I = N, S, I > 0}`.
* `IsSolution.lyapunov_le_initial`, `IsSolution.persistence`: `V(t) ≤ V(0)`, `I(t) ≥ m > 0`.
* `IsSolution.exists_lyapunov_le_exp`: exponential decay `V(t) ≤ V(0) e^{-c t}`.
* `IsSolution.tendsto_endemic_of_lyapunov`: global attractivity, `(S, I) → (S*, I*)`.
* `endemic_lyapunovStable`: Lyapunov stability of `(S*, I*)` on the segment.
* `endemic_globallyAsymptoticallyStable`: stability and global attractivity together.

## References

* B. S. Goh, *Global stability in two species interactions*, J. Math. Biol. 3 (1976) 313–318.
* A. Korobeinikov and G. C. Wake, *Lyapunov functions and global stability for SIR, SIRS, and
  SIS epidemiological models*, Appl. Math. Lett. 15 (2002) 955–960.
* H. W. Hethcote, *The mathematics of infectious diseases*, SIAM Review 42 (2000) 599–653, §3.
-/

@[expose] public section

open Real Filter Set
open scoped Topology

namespace MathlibExt.Biology.Epidemiology.SIS

/-- The **Goh–Volterra Lyapunov function** of the SIS endemic equilibrium
`(S*, I*) = (N γ / β, N (1 - γ / β))`:
`V(S, I) = (S - S* - S* log (S / S*)) + (I - I* - I* log (I / I*))`. -/
noncomputable def lyapunov (β γ N S I : ℝ) : ℝ :=
  (S - N * γ / β - N * γ / β * log (S / (N * γ / β))) +
    (I - N * (1 - γ / β) - N * (1 - γ / β) * log (I / (N * (1 - γ / β))))

/-! ### The scalar Volterra function `x - a - a log (x / a)` -/

/-- `x - a - a log (x / a) ≥ 0` for `a, x > 0` (from `log y ≤ y - 1`). -/
private theorem volterra_nonneg {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    0 ≤ x - a - a * log (x / a) := by
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hx ha)) ha.le
  have e : a * (x / a - 1) = x - a := by field_simp
  linarith

/-- `x - a - a log (x / a) = 0` only at `x = a` (from `log y < y - 1` for `y ≠ 1`). -/
private theorem volterra_eq_zero_iff {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    x - a - a * log (x / a) = 0 ↔ x = a := by
  refine ⟨fun h => by_contra fun hne => ?_, fun h => by simp [h, div_self ha.ne']⟩
  have hne' : x / a ≠ 1 := fun h1 => hne (by rw [div_eq_one_iff_eq ha.ne'] at h1; exact h1)
  have h2 := mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos (div_pos hx ha) hne') ha
  have e : a * (x / a - 1) = x - a := by field_simp
  linarith

/-- Upper bound `x - a - a log (x / a) ≤ (x - a)² / x` (from `log y ≥ 1 - 1 / y`). -/
private theorem volterra_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    x - a - a * log (x / a) ≤ (x - a) ^ 2 / x := by
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos (div_pos hx ha)) ha.le
  have e : a * (1 - (x / a)⁻¹) = a - a ^ 2 / x := by field_simp
  have e2 : (x - a) ^ 2 / x = x - 2 * a + a ^ 2 / x := by field_simp; ring
  linarith

private theorem hasDerivAt_volterra {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    HasDerivAt (fun x => x - a - a * log (x / a)) (1 - a / s) s := by
  have hl : HasDerivAt (fun x => log (x / a)) (1 / a / (s / a)) s :=
    ((hasDerivAt_id' s).div_const a).log (div_pos hs ha).ne'
  convert ((hasDerivAt_id' s).sub_const a).sub (hl.const_mul a) using 1
  field_simp

/-- Lower bound `(x - a)² ≤ 2 M (x - a - a log (x / a))` for `0 < x ≤ M`, `0 < a ≤ M`: the
difference has derivative `2 (x - a) (M - x) / x`, so it is minimal (`= 0`) at `x = a`. -/
private theorem sq_le_volterra {a x M : ℝ} (ha : 0 < a) (hx : 0 < x) (haM : a ≤ M)
    (hxM : x ≤ M) : (x - a) ^ 2 ≤ 2 * M * (x - a - a * log (x / a)) := by
  let φ : ℝ → ℝ := fun y => 2 * M * (y - a - a * log (y / a)) - (y - a) ^ 2
  have hφa : φ a = 0 := by simp [φ, div_self ha.ne']
  have hd : ∀ y, 0 < y → HasDerivAt φ (2 * (y - a) * (M - y) / y) y := by
    intro y hy
    have := ((hasDerivAt_volterra ha hy).const_mul (2 * M)).sub
      (((hasDerivAt_id' y).sub_const a).pow 2)
    convert this using 1
    field_simp
    ring
  suffices 0 ≤ φ x by simp only [φ] at this; linarith
  rcases le_total a x with hax | hxa
  · have hmono : MonotoneOn φ (Icc a x) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun y => 2 * (y - a) * (M - y) / y)
        (convex_Icc a x)
        (fun y hy => (hd y (by linarith [hy.1])).continuousAt.continuousWithinAt)
        (fun y hy => ?_) (fun y hy => ?_) <;> rw [interior_Icc] at hy
      · exact (hd y (by linarith [hy.1])).hasDerivWithinAt
      · exact div_nonneg (mul_nonneg (by linarith [hy.1]) (by linarith [hy.2])) (by linarith [hy.1])
    linarith [hmono ⟨le_rfl, hax⟩ ⟨hax, le_rfl⟩ hax]
  · have hanti : AntitoneOn φ (Icc x a) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun y => 2 * (y - a) * (M - y) / y)
        (convex_Icc x a)
        (fun y hy => (hd y (by linarith [hy.1])).continuousAt.continuousWithinAt)
        (fun y hy => ?_) (fun y hy => ?_) <;> rw [interior_Icc] at hy
      · exact (hd y (by linarith [hy.1])).hasDerivWithinAt
      · exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith [hy.2]) (by linarith [hy.2]))
          (by linarith [hy.1])
    linarith [hanti ⟨le_rfl, hxa⟩ ⟨hxa, le_rfl⟩ hxa]

/-- On `x + y = a + b`, the sum of the two Volterra functions is at most
`(x - a)² (x + y) / (x y)`. -/
private theorem volterra_add_le {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x)
    (hy : 0 < y) (hsum : x + y = a + b) :
    (x - a - a * log (x / a)) + (y - b - b * log (y / b)) ≤ (x - a) ^ 2 * (x + y) / (x * y) := by
  have h1 := volterra_le ha hx
  have h2 := volterra_le hb hy
  have hyb : (y - b) ^ 2 = (x - a) ^ 2 := by rw [show y - b = -(x - a) by linarith, neg_sq]
  have e : (x - a) ^ 2 / x + (y - b) ^ 2 / y = (x - a) ^ 2 * (x + y) / (x * y) := by
    rw [hyb]; field_simp; ring
  linarith

/-- A function with nonpositive derivative on `[0, ∞)` is nonincreasing there. -/
private theorem le_of_hasDerivAt_nonpos {f f' : ℝ → ℝ} (hf : ∀ t, 0 ≤ t → HasDerivAt f (f' t) t)
    (hf' : ∀ t, 0 ≤ t → f' t ≤ 0) {t : ℝ} (ht : 0 ≤ t) : f t ≤ f 0 :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hf x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hf' x (interior_subset hx)) (le_refl (0 : ℝ)) ht ht

/-! ### The equilibrium and the Lyapunov function -/

section Equilibrium

variable {β γ N : ℝ}

private theorem endemicS_pos (hγ : 0 < γ) (hγβ : γ < β) (hN : 0 < N) : 0 < N * γ / β :=
  div_pos (mul_pos hN hγ) (hγ.trans hγβ)

private theorem endemicI_pos (hγ : 0 < γ) (hγβ : γ < β) (hN : 0 < N) :
    0 < N * (1 - γ / β) :=
  mul_pos hN (sub_pos.2 ((div_lt_one (hγ.trans hγβ)).2 hγβ))

private theorem endemicI_le (hγ : 0 < γ) (hγβ : γ < β) (hN : 0 < N) : N * (1 - γ / β) ≤ N := by
  have : 0 ≤ γ / β := div_nonneg hγ.le (hγ.trans hγβ).le
  nlinarith

private theorem endemic_sum (hβ : β ≠ 0) : N * γ / β + N * (1 - γ / β) = N := by
  field_simp; ring

/-- **`V ≥ 0`** on the positive orthant, for `0 < γ < β` (`R₀ > 1`) and `N > 0`. -/
theorem lyapunov_nonneg (hγ : 0 < γ) (hγβ : γ < β) (hN : 0 < N) {S I : ℝ} (hS : 0 < S)
    (hI : 0 < I) : 0 ≤ lyapunov β γ N S I :=
  add_nonneg (volterra_nonneg (endemicS_pos hγ hγβ hN) hS)
    (volterra_nonneg (endemicI_pos hγ hγβ hN) hI)

/-- **`V` vanishes only at the endemic equilibrium** on the positive orthant. -/
theorem lyapunov_eq_zero_iff (hγ : 0 < γ) (hγβ : γ < β) (hN : 0 < N) {S I : ℝ} (hS : 0 < S)
    (hI : 0 < I) : lyapunov β γ N S I = 0 ↔ S = N * γ / β ∧ I = N * (1 - γ / β) := by
  have h1 := volterra_nonneg (endemicS_pos hγ hγβ hN) hS
  have h2 := volterra_nonneg (endemicI_pos hγ hγβ hN) hI
  rw [lyapunov, add_eq_zero_iff_of_nonneg h1 h2, volterra_eq_zero_iff (endemicS_pos hγ hγβ hN) hS,
    volterra_eq_zero_iff (endemicI_pos hγ hγβ hN) hI]

/-- **The Lyapunov derivative is nonpositive**: `-β (S - S*)² / S ≤ 0` for `β ≥ 0`, `S > 0`. -/
theorem lyapunovDeriv_nonpos (hβ : 0 ≤ β) {S : ℝ} (hS : 0 < S) :
    -(β * (S - N * γ / β) ^ 2 / S) ≤ 0 :=
  neg_nonpos.2 (div_nonneg (mul_nonneg hβ (sq_nonneg _)) hS.le)

/-- **The Lyapunov derivative vanishes only at the equilibrium**: on the segment `S + I = N`
with `S > 0` and `β > 0`, `-β (S - S*)² / S = 0` iff `(S, I) = (S*, I*)`. -/
theorem lyapunovDeriv_eq_zero_iff (hβ : 0 < β) {S I : ℝ} (hS : 0 < S) (hSI : S + I = N) :
    -(β * (S - N * γ / β) ^ 2 / S) = 0 ↔ S = N * γ / β ∧ I = N * (1 - γ / β) := by
  have hsum := endemic_sum (N := N) (γ := γ) hβ.ne'
  rw [neg_eq_zero, div_eq_zero_iff, mul_eq_zero, pow_eq_zero_iff two_ne_zero, sub_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact absurd h hβ.ne'
    · exact ⟨h, by linarith⟩
    · exact absurd h hS.ne'
  · rintro ⟨h, -⟩; exact Or.inl (Or.inr h)

end Equilibrium

/-! ### Forward invariance of the open segment -/

private theorem sisInfected_pos {β γ N I₀ t : ℝ} (hβ : 0 ≤ β) (hN : 0 < N) (hI₀ : 0 < I₀)
    (ht : 0 ≤ t) : 0 < sisInfected β γ N I₀ t :=
  div_pos (mul_pos hI₀ (exp_pos _)) (by linarith [one_le_sisDenom (γ := γ) hβ hN hI₀.le ht])

private theorem sisInfected_lt {β γ N I₀ t : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hN : 0 < N)
    (hI₀ : 0 ≤ I₀) (hI₀N : I₀ < N) (ht : 0 ≤ t) : sisInfected β γ N I₀ t < N := by
  have hD := one_le_sisDenom (γ := γ) hβ hN hI₀ ht
  have hφ := growthIntegral_nonneg (β - γ) ht
  have he := exp_eq_one_add_mul_growthIntegral (β - γ) t
  rw [sisInfected, div_lt_iff₀ (by linarith), mul_add, mul_one, he]
  have hNβ : N * (β * I₀ / N * growthIntegral (β - γ) t) = β * I₀ * growthIntegral (β - γ) t := by
    field_simp
  rw [hNβ]
  nlinarith [mul_nonneg (mul_nonneg hγ hI₀) hφ]

namespace IsSolution

variable {β γ N : ℝ} {S I : ℝ → ℝ}

/-- **Forward invariance of the open segment.** For `β, γ ≥ 0`, `N > 0`, a solution with
`S(0) + I(0) = N`, `S(0) > 0` and `I(0) > 0` keeps `S(t) > 0` and `I(t) > 0` for all `t ≥ 0`.
(Via the explicit solution `IsSolution.infected_eq_sisInfected`.) -/
theorem pos_of_pos (h : IsSolution β γ N S I) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hN : 0 < N)
    (hS : S 0 + I 0 = N) (hS0 : 0 < S 0) (hI0 : 0 < I 0) {t : ℝ} (ht : 0 ≤ t) :
    0 < S t ∧ 0 < I t := by
  have hIt := h.infected_eq_sisInfected hβ hN hS hI0.le ht
  have hT := h.total_eq ht
  refine ⟨?_, hIt ▸ sisInfected_pos hβ hN hI0 ht⟩
  have := sisInfected_lt (γ := γ) hβ hγ hN hI0.le (by linarith) ht
  rw [← hIt] at this
  linarith

/-- **Derivative of the Lyapunov function along solutions.** For `0 < γ < β`, `N > 0`, a
solution with `S(0) + I(0) = N` and a time `t ≥ 0` with `S(t), I(t) > 0`,
`d/dt V(S(t), I(t)) = -β (S(t) - S*)² / S(t)`. -/
theorem hasDerivAt_lyapunov (h : IsSolution β γ N S I) (hγ : 0 < γ) (hγβ : γ < β) (hN : 0 < N)
    (hS : S 0 + I 0 = N) {t : ℝ} (ht : 0 ≤ t) (hSt : 0 < S t) (hIt : 0 < I t) :
    HasDerivAt (fun s => lyapunov β γ N (S s) (I s)) (-(β * (S t - N * γ / β) ^ 2 / S t)) t := by
  have hβ : 0 < β := hγ.trans hγβ
  have hSs := endemicS_pos hγ hγβ hN
  have hIs := endemicI_pos hγ hγβ hN
  have hlS := ((h.hasDerivAt_susceptible t ht).div_const (N * γ / β)).log (div_pos hSt hSs).ne'
  have hlI := ((h.hasDerivAt_infected t ht).div_const (N * (1 - γ / β))).log
    (div_pos hIt hIs).ne'
  refine ((((h.hasDerivAt_susceptible t ht).sub_const _).sub (hlS.const_mul (N * γ / β))).add
    (((h.hasDerivAt_infected t ht).sub_const _).sub
      (hlI.const_mul (N * (1 - γ / β))))).congr_deriv ?_
  have hT : I t = N - S t := by linarith [h.total_eq ht]
  have hIt' : N - S t ≠ 0 := by rw [← hT]; exact hIt.ne'
  have hβγ : β - γ ≠ 0 := sub_ne_zero.2 hγβ.ne'
  have hβγ' : 1 - γ / β ≠ 0 := hIs.ne' ∘ fun h0 => by rw [h0, mul_zero]
  rw [hT]
  field_simp
  ring

variable (h : IsSolution β γ N S I) (hγ : 0 < γ) (hγβ : γ < β) (hN : 0 < N)
  (hS : S 0 + I 0 = N) (hS0 : 0 < S 0) (hI0 : 0 < I 0)
include h hγ hγβ hN hS hS0 hI0

/-- **`V` is nonincreasing along solutions**: `V(S(t), I(t)) ≤ V(S(0), I(0))` for `t ≥ 0`. -/
theorem lyapunov_le_initial {t : ℝ} (ht : 0 ≤ t) :
    lyapunov β γ N (S t) (I t) ≤ lyapunov β γ N (S 0) (I 0) :=
  le_of_hasDerivAt_nonpos (f := fun s => lyapunov β γ N (S s) (I s))
    (fun _ hs => h.hasDerivAt_lyapunov hγ hγβ hN hS hs
      (h.pos_of_pos (hγ.trans hγβ).le hγ.le hN hS hS0 hI0 hs).1
      (h.pos_of_pos (hγ.trans hγβ).le hγ.le hN hS hS0 hI0 hs).2)
    (fun _ hs => lyapunovDeriv_nonpos (hγ.trans hγβ).le
      (h.pos_of_pos (hγ.trans hγβ).le hγ.le hN hS hS0 hI0 hs).1) ht

/-- **Uniform persistence.** Along a solution in the open segment, the infectives stay above
`m = I* exp (-(V(0) + I*) / I*) > 0` for all `t ≥ 0`. -/
theorem persistence {t : ℝ} (ht : 0 ≤ t) :
    N * (1 - γ / β) *
        exp (-(lyapunov β γ N (S 0) (I 0) + N * (1 - γ / β)) / (N * (1 - γ / β))) ≤ I t := by
  have ha := endemicI_pos hγ hγβ hN
  have hpos := h.pos_of_pos (hγ.trans hγβ).le hγ.le hN hS hS0 hI0 ht
  have hV := h.lyapunov_le_initial hγ hγβ hN hS hS0 hI0 ht
  have hgS := volterra_nonneg (endemicS_pos hγ hγβ hN) hpos.1
  set a := N * (1 - γ / β)
  set V0 := lyapunov β γ N (S 0) (I 0)
  have hgI : I t - a - a * log (I t / a) ≤ V0 := by unfold lyapunov at hV; linarith
  have hlog : -(V0 + a) / a ≤ log (I t / a) := by
    rw [div_le_iff₀ ha]; nlinarith [hpos.2]
  have := (Real.le_log_iff_exp_le (div_pos hpos.2 ha)).1 hlog
  rw [le_div_iff₀ ha] at this
  linarith

/-- **Exponential decay of the Lyapunov function.** There is `c > 0` with
`V(S(t), I(t)) ≤ V(S(0), I(0)) e^{-c t}` for all `t ≥ 0` (take `c = β m / N`, `m` the
persistence bound). -/
theorem exists_lyapunov_le_exp :
    ∃ c > 0, ∀ t, 0 ≤ t →
      lyapunov β γ N (S t) (I t) ≤ lyapunov β γ N (S 0) (I 0) * exp (-(c * t)) := by
  have hβ : 0 < β := hγ.trans hγβ
  have ha := endemicS_pos hγ hγβ hN
  have hb := endemicI_pos hγ hγβ hN
  set m := N * (1 - γ / β) *
    exp (-(lyapunov β γ N (S 0) (I 0) + N * (1 - γ / β)) / (N * (1 - γ / β))) with hm_def
  have hm : 0 < m := mul_pos hb (exp_pos _)
  set c := β * m / N with hc_def
  have hc : 0 < c := by positivity
  refine ⟨c, hc, fun t ht => ?_⟩
  have hpos := fun s (hs : 0 ≤ s) => h.pos_of_pos hβ.le hγ.le hN hS hS0 hI0 hs
  let F : ℝ → ℝ := fun s => lyapunov β γ N (S s) (I s) * exp (c * s)
  have hF : ∀ s, 0 ≤ s → HasDerivAt F
      (-(β * (S s - N * γ / β) ^ 2 / S s) * exp (c * s) +
        lyapunov β γ N (S s) (I s) * (exp (c * s) * c)) s := by
    intro s hs
    have he : HasDerivAt (fun s => exp (c * s)) (exp (c * s) * c) s := by
      simpa using ((hasDerivAt_id s).const_mul c).exp
    exact (h.hasDerivAt_lyapunov hγ hγβ hN hS hs (hpos s hs).1 (hpos s hs).2).mul he
  have hF' : ∀ s, 0 ≤ s → -(β * (S s - N * γ / β) ^ 2 / S s) * exp (c * s) +
      lyapunov β γ N (S s) (I s) * (exp (c * s) * c) ≤ 0 := by
    intro s hs
    obtain ⟨hSs, hIs⟩ := hpos s hs
    have hT : S s + I s = N := by linarith [h.total_eq hs]
    have hmI := h.persistence hγ hγβ hN hS hS0 hI0 hs
    have hVle : lyapunov β γ N (S s) (I s) ≤
        (S s - N * γ / β) ^ 2 * (S s + I s) / (S s * I s) :=
      volterra_add_le ha hb hSs hIs (by rw [hT, endemic_sum hβ.ne'])
    have key : c * lyapunov β γ N (S s) (I s) ≤ β * (S s - N * γ / β) ^ 2 / S s := by
      calc c * lyapunov β γ N (S s) (I s)
          ≤ c * ((S s - N * γ / β) ^ 2 * (S s + I s) / (S s * I s)) :=
            mul_le_mul_of_nonneg_left hVle hc.le
        _ = β * (S s - N * γ / β) ^ 2 / S s * (m / I s) := by
            rw [hT, hc_def]; field_simp
        _ ≤ β * (S s - N * γ / β) ^ 2 / S s * 1 :=
            mul_le_mul_of_nonneg_left ((div_le_one hIs).2 hmI)
              (div_nonneg (mul_nonneg hβ.le (sq_nonneg _)) hSs.le)
        _ = β * (S s - N * γ / β) ^ 2 / S s := mul_one _
    have he := exp_pos (c * s)
    nlinarith
  have := le_of_hasDerivAt_nonpos hF hF' ht
  simp only [F, mul_zero, exp_zero, mul_one] at this
  rw [show -(c * t) = -(c * t) from rfl, Real.exp_neg, ← div_eq_mul_inv,
    le_div_iff₀ (exp_pos _)]
  exact this

/-- `(I(t) - I*)² ≤ 2 N V(S(t), I(t))` along a solution in the open segment. -/
private theorem sq_sub_le_lyapunov {t : ℝ} (ht : 0 ≤ t) :
    (I t - N * (1 - γ / β)) ^ 2 ≤ 2 * N * lyapunov β γ N (S t) (I t) := by
  have hpos := h.pos_of_pos (hγ.trans hγβ).le hγ.le hN hS hS0 hI0 ht
  have hT : S t + I t = N := by linarith [h.total_eq ht]
  have h1 := sq_le_volterra (endemicI_pos hγ hγβ hN) hpos.2 (endemicI_le hγ hγβ hN)
    (by linarith [hpos.1])
  have h2 := volterra_nonneg (endemicS_pos hγ hγβ hN) hpos.1
  unfold lyapunov
  nlinarith

/-- **Global attractivity via the Lyapunov function.** If `γ > 0` and `R₀ = β / γ > 1`, every
solution of the SIS model starting in the open segment `{S + I = N, S > 0, I > 0}` of the
positive orthant converges to the endemic equilibrium `(S*, I*) = (N γ / β, N (1 - γ / β))`. -/
theorem tendsto_endemic_of_lyapunov :
    Tendsto (fun t => (S t, I t)) atTop (𝓝 (N * γ / β, N * (1 - γ / β))) := by
  obtain ⟨c, hc, hdec⟩ := h.exists_lyapunov_le_exp hγ hγβ hN hS hS0 hI0
  set V0 := lyapunov β γ N (S 0) (I 0)
  have hlim : Tendsto (fun t => 2 * N * (V0 * exp (-(c * t)))) atTop (𝓝 0) := by
    have := (tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)).const_mul V0
    simpa using this.const_mul (2 * N)
  have hsq : Tendsto (fun t => (I t - N * (1 - γ / β)) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun t => sq_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (h.sq_sub_le_lyapunov hγ hγβ hN hS hS0 hI0 ht).trans
      (mul_le_mul_of_nonneg_left (hdec t ht) (by positivity))
  have hI : Tendsto I atTop (𝓝 (N * (1 - γ / β))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have := hsq.sqrt
    simp only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] at this
    simpa [Real.norm_eq_abs] using this
  have hSl : Tendsto S atTop (𝓝 (N * γ / β)) := by
    have := hI.const_sub N
    rw [show N - N * (1 - γ / β) = N * γ / β by ring] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    linarith [h.total_eq ht]
  exact hSl.prodMk_nhds hI

end IsSolution

/-! ### Lyapunov stability and global asymptotic stability -/

section Stability

variable {β γ N : ℝ}

/-- **Lyapunov stability of the endemic equilibrium.** For `γ > 0`, `R₀ = β / γ > 1` and
`N > 0`: for every `ε > 0` there is `δ > 0` such that every solution starting in the open
segment `{S + I = N, S > 0, I > 0}` within distance `δ` of `(S*, I*)` (in `ℝ × ℝ`) stays within
distance `ε` of it for all `t ≥ 0`. -/
theorem endemic_lyapunovStable (hγ : 0 < γ) (hR₀ : 1 < β / γ) (hN : 0 < N) :
    ∀ ε > 0, ∃ δ > 0, ∀ S I : ℝ → ℝ, IsSolution β γ N S I → S 0 + I 0 = N → 0 < S 0 →
      0 < I 0 → dist (S 0, I 0) (N * γ / β, N * (1 - γ / β)) < δ →
      ∀ t, 0 ≤ t → dist (S t, I t) (N * γ / β, N * (1 - γ / β)) < ε := by
  have hγβ : γ < β := (one_lt_div hγ).1 hR₀
  have hβ : 0 < β := hγ.trans hγβ
  have ha := endemicS_pos hγ hγβ hN
  have hb := endemicI_pos hγ hγβ hN
  have hsum := endemic_sum (N := N) (γ := γ) hβ.ne'
  set a := N * γ / β
  set b := N * (1 - γ / β)
  set K := 8 * N ^ 2 / (a * b) with hK_def
  have hK : 0 < K := by positivity
  intro ε hε
  refine ⟨min (min a b / 2) (ε / (K + 1)), by positivity, ?_⟩
  intro S I h hS hS0 hI0 hδ t ht
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff] at hδ
  obtain ⟨hSa, hIb⟩ := hδ
  have hmin1 : min a b / 2 ≤ a / 2 := by have := min_le_left a b; linarith
  have hmin2 : min a b / 2 ≤ b / 2 := by have := min_le_right a b; linarith
  have hS0' : a / 2 < S 0 := by
    have := (abs_lt.1 (hSa.trans_le (min_le_left _ _))).1; linarith
  have hI0' : b / 2 < I 0 := by
    have := (abs_lt.1 (hIb.trans_le (min_le_left _ _))).1; linarith
  have hd0 : |I 0 - b| < ε / (K + 1) := hIb.trans_le (min_le_right _ _)
  -- `V(0) ≤ (I(0) - I*)² N / (S(0) I(0)) ≤ 4 N (I(0) - I*)² / (a b)`.
  have hV0 : lyapunov β γ N (S 0) (I 0) ≤ (I 0 - b) ^ 2 * N / (S 0 * I 0) := by
    have := volterra_add_le ha hb hS0 hI0 (by rw [hS, hsum])
    have e : (S 0 - a) ^ 2 = (I 0 - b) ^ 2 := by
      rw [show S 0 - a = -(I 0 - b) by linarith, neg_sq]
    rw [e, hS] at this
    exact this
  have hV0' : (I 0 - b) ^ 2 * N / (S 0 * I 0) ≤ 4 * N * (I 0 - b) ^ 2 / (a * b) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : a * b ≤ 4 * (S 0 * I 0) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg (sq_nonneg (I 0 - b)) hN.le)]
  have hsq := h.sq_sub_le_lyapunov hγ hγβ hN hS hS0 hI0 ht
  have hle := h.lyapunov_le_initial hγ hγβ hN hS hS0 hI0 ht
  have hdt : (I t - b) ^ 2 ≤ K * (I 0 - b) ^ 2 := by
    have : 2 * N * (4 * N * (I 0 - b) ^ 2 / (a * b)) = K * (I 0 - b) ^ 2 := by
      rw [hK_def]; field_simp; ring
    nlinarith
  have hKd : K * (I 0 - b) ^ 2 < ε ^ 2 := by
    have h1 : (I 0 - b) ^ 2 < (ε / (K + 1)) ^ 2 := by
      rw [← sq_abs]; exact pow_lt_pow_left₀ hd0 (abs_nonneg _) two_ne_zero
    have h2 : K * (ε / (K + 1)) ^ 2 ≤ ε ^ 2 := by
      rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg ε, sq_nonneg K]
    nlinarith
  have hIt : |I t - b| < ε := abs_lt_of_sq_lt_sq (hdt.trans_lt hKd) hε.le
  have hT := h.total_eq ht
  have hSt : |S t - a| < ε := by
    rw [show S t - a = -(I t - b) by linarith, abs_neg]; exact hIt
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
  exact ⟨hSt, hIt⟩

/-- **Global asymptotic stability of the SIS endemic equilibrium.** If `γ > 0`,
`R₀ = β / γ > 1` and `N > 0`, the endemic equilibrium `(S*, I*) = (N γ / β, N (1 - γ / β))` is
Lyapunov stable and attracts every solution starting in the open segment
`{S + I = N, S > 0, I > 0}` of the positive orthant; both facts are proved from the
Goh–Volterra function `lyapunov`. -/
theorem endemic_globallyAsymptoticallyStable (hγ : 0 < γ) (hR₀ : 1 < β / γ) (hN : 0 < N) :
    (∀ ε > 0, ∃ δ > 0, ∀ S I : ℝ → ℝ, IsSolution β γ N S I → S 0 + I 0 = N → 0 < S 0 →
      0 < I 0 → dist (S 0, I 0) (N * γ / β, N * (1 - γ / β)) < δ →
      ∀ t, 0 ≤ t → dist (S t, I t) (N * γ / β, N * (1 - γ / β)) < ε) ∧
    (∀ S I : ℝ → ℝ, IsSolution β γ N S I → S 0 + I 0 = N → 0 < S 0 → 0 < I 0 →
      Tendsto (fun t => (S t, I t)) atTop (𝓝 (N * γ / β, N * (1 - γ / β)))) :=
  ⟨endemic_lyapunovStable hγ hR₀ hN, fun _ _ h hS hS0 hI0 =>
    h.tendsto_endemic_of_lyapunov hγ ((one_lt_div hγ).1 hR₀) hN hS hS0 hI0⟩

end Stability

end MathlibExt.Biology.Epidemiology.SIS
