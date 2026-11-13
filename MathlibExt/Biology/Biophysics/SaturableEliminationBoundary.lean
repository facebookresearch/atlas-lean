/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.MichaelisMenten
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Saturable elimination: monotone approach and the critical infusion rate `R = Vmax`

One-compartment saturable (Michaelis–Menten) elimination under constant infusion `R`,

  `C' = R - mmRate Vmax Km C = R - Vmax C / (Km + C)`,

with `Vmax, Km > 0`, is restated here minimally as the hypothesis
`hC : ∀ t, 0 ≤ t → HasDerivAt C (R - mmRate Vmax Km (C t)) t`, using the canonical rate law
`MathlibExt.Biology.Dynamics.MichaelisMenten.mmRate`. This hypothesis is definitionally the
predicate `SaturableElimination.IsSolution Vmax Km R C` of the sibling file (open as #1577),
which proves existence, uniqueness, nonnegativity, and exponential convergence to the steady
state. Equilibria are taken as an explicit `c ≥ 0` with `mmRate Vmax Km c = R`; for
`0 ≤ R < Vmax` this is `c = R Km / (Vmax - R)` (the sibling's `steadyConc`).

## Main results

Approach to the equilibrium (`R < Vmax`, forced by `lt_of_mmRate_eq`):

* `le_of_initial_le`, `le_of_le_initial`, `eq_of_initial_eq`: each side of `c`, and `c` itself,
  is invariant.
* `monotoneOn_of_initial_le`, `antitoneOn_of_le_initial`: the approach is monotone, from below
  for `0 ≤ C(0) ≤ c` and from above for `c ≤ C(0)`.
* `strictMonoOn_of_initial_lt`, `strictAntiOn_of_lt_initial`, `lt_of_initial_lt`,
  `lt_of_lt_initial`: strictly monotone, and `c` is never reached in finite time.
* `mul_exp_le_sub_of_initial_le`, `mul_exp_le_sub_of_le_initial`: the gap `|C(t) - c|` is at least
  `|C(0) - c| e^{-λ t}`, with `λ = (Vmax - R)/(Km + C(0))` from below and
  `λ = (Vmax - R)/(Km + c)` from above; together with the sibling's upper bound this pins the
  approach between two exponentials.
* `eventually_lt_of_mmRate_eq`: the equilibrium tends to `∞` as `R → Vmax⁻`.

The critical rate `R = Vmax`, where `(Km + C) C' = Vmax Km`:

* `sq_add_critical`, `eq_sqrt_critical`: the exact solution
  `(Km + C(t))² = (Km + C(0))² + 2 Vmax Km t`, i.e. `C(t) = √((Km + C(0))² + 2 Vmax Km t) - Km`.
* `strictMonoOn_critical`, `tendsto_atTop_critical`: strictly increasing and unbounded, so there
  is no steady state.
* `sqrt_sub_le_critical`, `le_add_sqrt_critical`:
  `√(2 Vmax Km t) - Km ≤ C(t) ≤ C(0) + √(2 Vmax Km t)`.
* `tendsto_div_sqrt_critical`, `tendsto_div_critical`: `C(t)/√t → √(2 Vmax Km)` and
  `C(t)/t → 0`. Accumulation at the critical rate is square-root, slower than the linear growth
  `C(t) ≥ C(0) + (R - Vmax) t` for `R > Vmax`.

## Source receipt

* Model and steady state `C_ss = Km R / (Vmax - R)`, with no steady state once `R ≥ Vmax`:
  M. Gibaldi and D. Perrier, *Pharmacokinetics*, 2nd ed., Marcel Dekker (1982), ch. 7
  ("Nonlinear pharmacokinetics"); M. Rowland and T. N. Tozer, *Clinical Pharmacokinetics and
  Pharmacodynamics*, 4th ed. (2011), ch. 20.
* Monotone approach: for a scalar autonomous equation `x' = f(x)` trajectories are monotone and
  approach equilibria without crossing them (S. H. Strogatz, *Nonlinear Dynamics and Chaos*,
  2nd ed. (2015), §2.2 and §2.6, "Impossibility of oscillations"). Here it is proved directly,
  with explicit exponential rates, by strict barriers
  (`image_le_of_deriv_right_lt_deriv_boundary`), so no uniqueness theorem is needed.
* Critical rate: separating variables in `C' = Vmax Km / (Km + C)` gives the integrated form
  `Km C + C² / 2 = Km C₀ + C₀² / 2 + Vmax Km t`, the infusion analogue of the integrated
  Michaelis–Menten equation (J. G. Wagner, *J. Pharmacokin. Biopharm.* 1 (1973) 103–121). The
  square-root law and its constants are derived in this file from that identity, not quoted.

This is a mathematical model only; it carries no dosing recommendation.
-/

@[expose] public section

open Real Set Filter Topology

namespace MathlibExt.Biology.Biophysics.SaturableEliminationBoundary

open MathlibExt.Biology.Dynamics.MichaelisMenten (mmRate mmRate_lt mmRate_strictMono)

variable {Vmax Km R c : ℝ}

private lemma sub_mmRate_of_mmRate_eq (hc : mmRate Vmax Km c = R) (hKc : Km + c ≠ 0) {y : ℝ}
    (hKy : Km + y ≠ 0) : R - mmRate Vmax Km y = (Vmax - R) * (c - y) / (Km + y) := by
  subst hc
  unfold mmRate
  field_simp
  ring

private lemma sub_mmRate_critical {y : ℝ} (hKy : Km + y ≠ 0) :
    Vmax - mmRate Vmax Km y = Vmax * Km / (Km + y) := by
  unfold mmRate
  field_simp
  ring

/-! ### Comparison helpers -/

/-- A function with nonnegative derivative on `[0, ∞)` is monotone there. -/
private lemma monotoneOn_Ici_of_nonneg {g g' : ℝ → ℝ} (hg : ∀ t, 0 ≤ t → HasDerivAt g (g' t) t)
    (hg' : ∀ t, 0 ≤ t → 0 ≤ g' t) : MonotoneOn g (Ici 0) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun x hx ↦ (hg x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ (hg x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx ↦ hg' x (interior_subset hx))

/-- A function with positive derivative on `[0, ∞)` is strictly monotone there. -/
private lemma strictMonoOn_Ici_of_pos {g g' : ℝ → ℝ} (hg : ∀ t, 0 ≤ t → HasDerivAt g (g' t) t)
    (hg' : ∀ t, 0 ≤ t → 0 < g' t) : StrictMonoOn g (Ici 0) :=
  strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
    (fun x hx ↦ (hg x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ (hg x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx ↦ hg' x (interior_subset hx))

/-- **Upper barrier.** If `C' = F(C)` on `[0, ∞)`, `C(0) ≤ ℓ` and `F < 0` just above `ℓ`, then
`C ≤ ℓ` on `[0, ∞)`. -/
private lemma le_of_barrier {C F : ℝ → ℝ} (hC : ∀ t, 0 ≤ t → HasDerivAt C (F (C t)) t)
    {ℓ δ : ℝ} (hδ : 0 < δ) (hF : ∀ y, ℓ < y → y < ℓ + δ → F y < 0) (h0 : C 0 ≤ ℓ) {t : ℝ}
    (ht : 0 ≤ t) : C t ≤ ℓ := by
  have key : ∀ ε, 0 < ε → ε < δ → C t ≤ ℓ + ε := by
    intro ε hε hεδ
    refine image_le_of_deriv_right_lt_deriv_boundary (f := C) (f' := fun x ↦ F (C x)) (a := 0)
      (b := t) (B := fun _ ↦ ℓ + ε) (B' := fun _ ↦ 0)
      (fun x hx ↦ (hC x hx.1).continuousAt.continuousWithinAt)
      (fun x hx ↦ (hC x hx.1).hasDerivWithinAt) (by linarith) (fun x ↦ hasDerivAt_const x _)
      (fun x _ hx ↦ hF _ (by rw [hx]; linarith) (by rw [hx]; linarith)) ⟨ht, le_rfl⟩
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  calc C t ≤ ℓ + min ε (δ / 2) :=
        key _ (lt_min hε (by linarith)) ((min_le_right _ _).trans_lt (by linarith))
    _ ≤ ℓ + ε := by gcongr; exact min_le_left _ _

/-- **Lower barrier.** If `C' = F(C)` on `[0, ∞)`, `ℓ ≤ C(0)` and `F > 0` just below `ℓ`, then
`ℓ ≤ C` on `[0, ∞)`. -/
private lemma ge_of_barrier {C F : ℝ → ℝ} (hC : ∀ t, 0 ≤ t → HasDerivAt C (F (C t)) t)
    {ℓ δ : ℝ} (hδ : 0 < δ) (hF : ∀ y, ℓ - δ < y → y < ℓ → 0 < F y) (h0 : ℓ ≤ C 0) {t : ℝ}
    (ht : 0 ≤ t) : ℓ ≤ C t := by
  have := le_of_barrier (C := fun s ↦ -C s) (F := fun y ↦ -F (-y)) (ℓ := -ℓ)
    (fun s hs ↦ by simpa using (hC s hs).fun_neg) hδ
    (fun y h1 h2 ↦ by have := hF (-y) (by linarith) (by linarith); linarith) (by linarith) ht
  linarith

/-! ### Approach to an equilibrium (`R < Vmax`)

Throughout, `c ≥ 0` is an equilibrium: `mmRate Vmax Km c = R`. Such a `c` exists iff
`0 ≤ R < Vmax`, and then `c = R Km / (Vmax - R)`. -/

section Equilibrium

variable {C : ℝ → ℝ} {t : ℝ}

/-- An equilibrium forces `R < Vmax` (elimination never reaches its capacity). -/
theorem lt_of_mmRate_eq (hV : 0 < Vmax) (hK : 0 < Km) (hc0 : 0 ≤ c)
    (hc : mmRate Vmax Km c = R) : R < Vmax :=
  hc ▸ mmRate_lt hV hK hc0

/-- Field sign above the equilibrium: `R - mmRate Vmax Km y < 0` for `y > c`. -/
private lemma field_neg (hV : 0 < Vmax) (hK : 0 < Km) (hc0 : 0 ≤ c)
    (hc : mmRate Vmax Km c = R) {y : ℝ} (hy : c < y) : R - mmRate Vmax Km y < 0 := by
  rw [sub_mmRate_of_mmRate_eq hc (by linarith) (by linarith)]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (sub_pos.2 (lt_of_mmRate_eq hV hK hc0 hc)) (by linarith))
    (by linarith)

/-- Field sign below the equilibrium: `R - mmRate Vmax Km y > 0` for `-Km < y < c`. -/
private lemma field_pos (hV : 0 < Vmax) (hK : 0 < Km) (hc0 : 0 ≤ c)
    (hc : mmRate Vmax Km c = R) {y : ℝ} (hKy : 0 < Km + y) (hy : y < c) :
    0 < R - mmRate Vmax Km y := by
  rw [sub_mmRate_of_mmRate_eq hc (by linarith) hKy.ne']
  exact div_pos (mul_pos (sub_pos.2 (lt_of_mmRate_eq hV hK hc0 hc)) (by linarith)) hKy

/-- **The region below the equilibrium is invariant.** If `C(0) ≤ c` then `C(t) ≤ c` for all
`t ≥ 0`. -/
theorem le_of_initial_le (hC : ∀ t, 0 ≤ t → HasDerivAt C (R - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (hc0 : 0 ≤ c) (hc : mmRate Vmax Km c = R) (h0 : C 0 ≤ c)
    (ht : 0 ≤ t) : C t ≤ c :=
  le_of_barrier (F := fun y ↦ R - mmRate Vmax Km y) hC one_pos
    (fun _ hy _ ↦ field_neg hV hK hc0 hc hy) h0 ht

/-- **The region above the equilibrium is invariant.** If `c ≤ C(0)` then `c ≤ C(t)` for all
`t ≥ 0`. -/
theorem le_of_le_initial (hC : ∀ t, 0 ≤ t → HasDerivAt C (R - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (hc0 : 0 ≤ c) (hc : mmRate Vmax Km c = R) (h0 : c ≤ C 0)
    (ht : 0 ≤ t) : c ≤ C t :=
  ge_of_barrier (F := fun y ↦ R - mmRate Vmax Km y) hC hK
    (fun _ h1 h2 ↦ field_pos hV hK hc0 hc (by linarith) h2) h0 ht

/-- **The equilibrium is invariant.** A solution starting at `c` stays at `c`. -/
theorem eq_of_initial_eq (hC : ∀ t, 0 ≤ t → HasDerivAt C (R - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (hc0 : 0 ≤ c) (hc : mmRate Vmax Km c = R) (h0 : C 0 = c)
    (ht : 0 ≤ t) : C t = c :=
  le_antisymm (le_of_initial_le hC hV hK hc0 hc h0.le ht)
    (le_of_le_initial hC hV hK hc0 hc h0.ge ht)

/-- Starting below the equilibrium, the solution never drops below its initial value. -/
theorem initial_le_of_initial_le (hC : ∀ t, 0 ≤ t → HasDerivAt C (R - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (hc0 : 0 ≤ c) (hc : mmRate Vmax Km c = R) (h00 : 0 ≤ C 0)
    (h0 : C 0 ≤ c) (ht : 0 ≤ t) : C 0 ≤ C t :=
  ge_of_barrier (F := fun y ↦ R - mmRate Vmax Km y) hC hK
    (fun _ h1 h2 ↦ field_pos hV hK hc0 hc (by linarith) (by linarith)) le_rfl ht

/-- Starting above the equilibrium, the solution never exceeds its initial value. -/
theorem le_initial_of_le_initial (hC : ∀ t, 0 ≤ t → HasDerivAt C (R - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (hc0 : 0 ≤ c) (hc : mmRate Vmax Km c = R) (h0 : c ≤ C 0)
    (ht : 0 ≤ t) : C t ≤ C 0 :=
  le_of_barrier (F := fun y ↦ R - mmRate Vmax Km y) hC one_pos
    (fun _ hy _ ↦ field_neg hV hK hc0 hc (by linarith)) le_rfl ht

/-- **Monotone approach from below.** For `0 ≤ C(0) ≤ c` the solution is nondecreasing on
`[0, ∞)`. -/
theorem monotoneOn_of_initial_le (hC : ∀ t, 0 ≤ t → HasDerivAt C (R - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (hc0 : 0 ≤ c) (hc : mmRate Vmax Km c = R) (h00 : 0 ≤ C 0)
    (h0 : C 0 ≤ c) : MonotoneOn C (Ici 0) := by
  refine monotoneOn_Ici_of_nonneg hC fun s hs ↦ ?_
  have h1 := le_of_initial_le hC hV hK hc0 hc h0 hs
  have h2 := initial_le_of_initial_le hC hV hK hc0 hc h00 h0 hs
  rw [sub_mmRate_of_mmRate_eq hc (by linarith) (by linarith)]
  exact div_nonneg (mul_nonneg (sub_pos.2 (lt_of_mmRate_eq hV hK hc0 hc)).le (by linarith))
    (by linarith)

/-- **Monotone approach from above.** For `c ≤ C(0)` the solution is nonincreasing on
`[0, ∞)`. -/
theorem antitoneOn_of_le_initial (hC : ∀ t, 0 ≤ t → HasDerivAt C (R - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (hc0 : 0 ≤ c) (hc : mmRate Vmax Km c = R) (h0 : c ≤ C 0) :
    AntitoneOn C (Ici 0) := by
  have := monotoneOn_Ici_of_nonneg (g := fun s ↦ -C s) (fun s hs ↦ (hC s hs).fun_neg) fun s hs ↦ by
    have h1 := le_of_le_initial hC hV hK hc0 hc h0 hs
    rw [sub_mmRate_of_mmRate_eq hc (by linarith) (by linarith), neg_nonneg]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sub_pos.2 (lt_of_mmRate_eq hV hK hc0 hc)).le
        (by linarith)) (by linarith)
  exact fun a ha b hb hab ↦ neg_le_neg_iff.1 (this ha hb hab)

/-- **The gap closes no faster than exponentially, from below.** For `0 ≤ C(0) ≤ c`,
`(c - C(0)) e^{-λ t} ≤ c - C(t)` with `λ = (Vmax - R) / (Km + C(0))`. -/
theorem mul_exp_le_sub_of_initial_le (hC : ∀ t, 0 ≤ t → HasDerivAt C (R - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (hc0 : 0 ≤ c) (hc : mmRate Vmax Km c = R) (h00 : 0 ≤ C 0)
    (h0 : C 0 ≤ c) (ht : 0 ≤ t) :
    (c - C 0) * exp (-((Vmax - R) / (Km + C 0)) * t) ≤ c - C t := by
  set L := (Vmax - R) / (Km + C 0) with hL
  have hRV := lt_of_mmRate_eq hV hK hc0 hc
  have hmono := monotoneOn_Ici_of_nonneg (g := fun s ↦ (c - C s) * exp (L * s))
    (g' := fun s ↦ (c - C s) * (L - (Vmax - R) / (Km + C s)) * exp (L * s))
    (fun s hs ↦ by
      have h2 := initial_le_of_initial_le hC hV hK hc0 hc h00 h0 hs
      have hd := ((hC s hs).const_sub c).mul ((hasDerivAt_id' s).const_mul L).exp
      convert hd using 1
      rw [sub_mmRate_of_mmRate_eq hc (by linarith) (by linarith)]
      have : Km + C s ≠ 0 := by linarith
      field_simp
      ring)
    (fun s hs ↦ by
      have h1 := le_of_initial_le hC hV hK hc0 hc h0 hs
      have h2 := initial_le_of_initial_le hC hV hK hc0 hc h00 h0 hs
      have h3 : (Vmax - R) / (Km + C s) ≤ L :=
        div_le_div_of_nonneg_left (sub_pos.2 hRV).le (by linarith) (by linarith)
      have h4 : 0 ≤ c - C s := by linarith
      have h5 : 0 ≤ L - (Vmax - R) / (Km + C s) := by linarith
      positivity)
  have hg := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
  simp only [mul_zero, exp_zero, mul_one] at hg
  calc (c - C 0) * exp (-L * t) ≤ (c - C t) * exp (L * t) * exp (-L * t) :=
        mul_le_mul_of_nonneg_right hg (exp_pos _).le
    _ = c - C t := by rw [mul_assoc, ← exp_add]; simp

/-- **The gap closes no faster than exponentially, from above.** For `c ≤ C(0)`,
`(C(0) - c) e^{-λ t} ≤ C(t) - c` with `λ = (Vmax - R) / (Km + c)`. -/
theorem mul_exp_le_sub_of_le_initial (hC : ∀ t, 0 ≤ t → HasDerivAt C (R - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (hc0 : 0 ≤ c) (hc : mmRate Vmax Km c = R) (h0 : c ≤ C 0)
    (ht : 0 ≤ t) : (C 0 - c) * exp (-((Vmax - R) / (Km + c)) * t) ≤ C t - c := by
  set L := (Vmax - R) / (Km + c) with hL
  have hRV := lt_of_mmRate_eq hV hK hc0 hc
  have hmono := monotoneOn_Ici_of_nonneg (g := fun s ↦ (C s - c) * exp (L * s))
    (g' := fun s ↦ (C s - c) * (L - (Vmax - R) / (Km + C s)) * exp (L * s))
    (fun s hs ↦ by
      have h1 := le_of_le_initial hC hV hK hc0 hc h0 hs
      have hd := ((hC s hs).sub_const c).mul ((hasDerivAt_id' s).const_mul L).exp
      convert hd using 1
      rw [sub_mmRate_of_mmRate_eq hc (by linarith) (by linarith)]
      have : Km + C s ≠ 0 := by linarith
      have : Km + c ≠ 0 := by linarith
      field_simp
      ring)
    (fun s hs ↦ by
      have h1 := le_of_le_initial hC hV hK hc0 hc h0 hs
      have h3 : (Vmax - R) / (Km + C s) ≤ L :=
        div_le_div_of_nonneg_left (sub_pos.2 hRV).le (by linarith) (by linarith)
      have h4 : 0 ≤ C s - c := by linarith
      have h5 : 0 ≤ L - (Vmax - R) / (Km + C s) := by linarith
      positivity)
  have hg := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
  simp only [mul_zero, exp_zero, mul_one] at hg
  calc (C 0 - c) * exp (-L * t) ≤ (C t - c) * exp (L * t) * exp (-L * t) :=
        mul_le_mul_of_nonneg_right hg (exp_pos _).le
    _ = C t - c := by rw [mul_assoc, ← exp_add]; simp

/-- Starting strictly below the equilibrium, the solution stays strictly below it. -/
theorem lt_of_initial_lt (hC : ∀ t, 0 ≤ t → HasDerivAt C (R - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (hc0 : 0 ≤ c) (hc : mmRate Vmax Km c = R) (h00 : 0 ≤ C 0)
    (h0 : C 0 < c) (ht : 0 ≤ t) : C t < c := by
  have := mul_exp_le_sub_of_initial_le hC hV hK hc0 hc h00 h0.le ht
  have : 0 < (c - C 0) * exp (-((Vmax - R) / (Km + C 0)) * t) :=
    mul_pos (sub_pos.2 h0) (exp_pos _)
  linarith

/-- Starting strictly above the equilibrium, the solution stays strictly above it. -/
theorem lt_of_lt_initial (hC : ∀ t, 0 ≤ t → HasDerivAt C (R - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (hc0 : 0 ≤ c) (hc : mmRate Vmax Km c = R) (h0 : c < C 0)
    (ht : 0 ≤ t) : c < C t := by
  have := mul_exp_le_sub_of_le_initial hC hV hK hc0 hc h0.le ht
  have : 0 < (C 0 - c) * exp (-((Vmax - R) / (Km + c)) * t) :=
    mul_pos (sub_pos.2 h0) (exp_pos _)
  linarith

/-- **Strictly monotone approach from below.** For `0 ≤ C(0) < c` the solution is strictly
increasing on `[0, ∞)`. -/
theorem strictMonoOn_of_initial_lt (hC : ∀ t, 0 ≤ t → HasDerivAt C (R - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (hc0 : 0 ≤ c) (hc : mmRate Vmax Km c = R) (h00 : 0 ≤ C 0)
    (h0 : C 0 < c) : StrictMonoOn C (Ici 0) :=
  strictMonoOn_Ici_of_pos hC fun s hs ↦ field_pos hV hK hc0 hc
    (by linarith [initial_le_of_initial_le hC hV hK hc0 hc h00 h0.le hs])
    (lt_of_initial_lt hC hV hK hc0 hc h00 h0 hs)

/-- **Strictly monotone approach from above.** For `c < C(0)` the solution is strictly
decreasing on `[0, ∞)`. -/
theorem strictAntiOn_of_lt_initial (hC : ∀ t, 0 ≤ t → HasDerivAt C (R - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (hc0 : 0 ≤ c) (hc : mmRate Vmax Km c = R) (h0 : c < C 0) :
    StrictAntiOn C (Ici 0) := by
  have := strictMonoOn_Ici_of_pos (g := fun s ↦ -C s) (fun s hs ↦ (hC s hs).fun_neg)
    fun s hs ↦ neg_pos.2 (field_neg hV hK hc0 hc (lt_of_lt_initial hC hV hK hc0 hc h0 hs))
  exact fun a ha b hb hab ↦ neg_lt_neg_iff.1 (this ha hb hab)

end Equilibrium

/-- **Equilibria blow up at the critical rate.** For every level `M`, all infusion rates `R`
close enough to `Vmax` from below have every nonnegative equilibrium above `M`: the steady state
`c = R Km / (Vmax - R)` tends to `∞` as `R → Vmax⁻`. -/
theorem eventually_lt_of_mmRate_eq (hV : 0 < Vmax) (hK : 0 < Km) (M : ℝ) :
    ∀ᶠ R in 𝓝[<] Vmax, ∀ c, 0 ≤ c → mmRate Vmax Km c = R → M < c := by
  have hm : mmRate Vmax Km (max M 0) < Vmax := mmRate_lt hV hK (le_max_right _ _)
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hm)] with R hR c hc0 hc
  refine (le_max_left M 0).trans_lt (lt_of_not_ge fun h ↦ ?_)
  have := (mmRate_strictMono hV hK).monotoneOn (mem_Ici.2 hc0) (mem_Ici.2 (le_max_right M 0)) h
  rw [hc] at this
  exact absurd (mem_Ioi.1 hR) (not_lt.2 this)

/-! ### The critical rate `R = Vmax`

At `R = Vmax` the field is `Vmax - mmRate Vmax Km C = Vmax Km / (Km + C) > 0`, so
`(Km + C) C' = Vmax Km` and the equation integrates exactly. -/

section Critical

variable {C : ℝ → ℝ} {t : ℝ}

private lemma field_critical_pos (hV : 0 < Vmax) (hK : 0 < Km) {y : ℝ} (hKy : 0 < Km + y) :
    0 < Vmax - mmRate Vmax Km y := by
  rw [sub_mmRate_critical hKy.ne']
  exact div_pos (mul_pos hV hK) hKy

/-- At the critical rate the solution never drops below its initial value. -/
theorem initial_le_critical (hC : ∀ t, 0 ≤ t → HasDerivAt C (Vmax - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (h00 : 0 ≤ C 0) (ht : 0 ≤ t) : C 0 ≤ C t :=
  ge_of_barrier (F := fun y ↦ Vmax - mmRate Vmax Km y) hC hK
    (fun _ h1 _ ↦ field_critical_pos hV hK (by linarith)) le_rfl ht

/-- At the critical rate the solution is strictly increasing on `[0, ∞)`. -/
theorem strictMonoOn_critical (hC : ∀ t, 0 ≤ t → HasDerivAt C (Vmax - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (h00 : 0 ≤ C 0) : StrictMonoOn C (Ici 0) :=
  strictMonoOn_Ici_of_pos hC fun s hs ↦
    field_critical_pos hV hK (by linarith [initial_le_critical hC hV hK h00 hs])

/-- **Exact integral at the critical rate.** `(Km + C(t))² = (Km + C(0))² + 2 Vmax Km t`. -/
theorem sq_add_critical (hC : ∀ t, 0 ≤ t → HasDerivAt C (Vmax - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (h00 : 0 ≤ C 0) (ht : 0 ≤ t) :
    (Km + C t) ^ 2 = (Km + C 0) ^ 2 + 2 * Vmax * Km * t := by
  have hd : ∀ s, 0 ≤ s → HasDerivAt (fun s ↦ (Km + C s) ^ 2 - 2 * Vmax * Km * s) 0 s := by
    intro s hs
    have h2 := initial_le_critical hC hV hK h00 hs
    have hd := (((hC s hs).const_add Km).pow 2).sub ((hasDerivAt_id' s).const_mul (2 * Vmax * Km))
    convert hd using 1
    rw [sub_mmRate_critical (by linarith)]
    have : Km + C s ≠ 0 := by linarith
    field_simp
    ring
  have h1 := monotoneOn_Ici_of_nonneg hd (fun _ _ ↦ le_rfl) (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
  have h2 := monotoneOn_Ici_of_nonneg (fun s hs ↦ (hd s hs).fun_neg) (fun _ _ ↦ by simp)
    (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
  simp only [mul_zero, sub_zero, neg_le_neg_iff] at h1 h2
  linarith

/-- **Closed form at the critical rate.** `C(t) = √((Km + C(0))² + 2 Vmax Km t) - Km`. -/
theorem eq_sqrt_critical (hC : ∀ t, 0 ≤ t → HasDerivAt C (Vmax - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (h00 : 0 ≤ C 0) (ht : 0 ≤ t) :
    C t = √((Km + C 0) ^ 2 + 2 * Vmax * Km * t) - Km := by
  rw [← sq_add_critical hC hV hK h00 ht,
    Real.sqrt_sq (by linarith [initial_le_critical hC hV hK h00 ht])]
  ring

/-- Lower square-root bound at the critical rate: `√(2 Vmax Km t) - Km ≤ C(t)`. -/
theorem sqrt_sub_le_critical (hC : ∀ t, 0 ≤ t → HasDerivAt C (Vmax - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (h00 : 0 ≤ C 0) (ht : 0 ≤ t) :
    √(2 * Vmax * Km * t) - Km ≤ C t := by
  rw [eq_sqrt_critical hC hV hK h00 ht]
  have := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg (Km + C 0)) :
    2 * Vmax * Km * t ≤ (Km + C 0) ^ 2 + 2 * Vmax * Km * t)
  linarith

/-- Upper square-root bound at the critical rate: `C(t) ≤ C(0) + √(2 Vmax Km t)`. -/
theorem le_add_sqrt_critical (hC : ∀ t, 0 ≤ t → HasDerivAt C (Vmax - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (h00 : 0 ≤ C 0) (ht : 0 ≤ t) :
    C t ≤ C 0 + √(2 * Vmax * Km * t) := by
  have hs := sq_add_critical hC hV hK h00 ht
  have hq0 : 0 ≤ √(2 * Vmax * Km * t) := Real.sqrt_nonneg _
  have hq2 : √(2 * Vmax * Km * t) ^ 2 = 2 * Vmax * Km * t := Real.sq_sqrt (by positivity)
  have hle : (Km + C t) ^ 2 ≤ (Km + C 0 + √(2 * Vmax * Km * t)) ^ 2 := by
    rw [hs]
    nlinarith [mul_nonneg (by linarith : 0 ≤ Km + C 0) hq0]
  have := (pow_le_pow_iff_left₀ (by linarith [initial_le_critical hC hV hK h00 ht])
    (by linarith) two_ne_zero).1 hle
  linarith

/-- **No steady state at the critical rate: unbounded accumulation.** For `R = Vmax` every
solution with `C(0) ≥ 0` tends to `∞`. -/
theorem tendsto_atTop_critical (hC : ∀ t, 0 ≤ t → HasDerivAt C (Vmax - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (h00 : 0 ≤ C 0) : Tendsto C atTop atTop := by
  have hlow : Tendsto (fun t ↦ √(2 * Vmax * Km * t) + -Km) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      (tendsto_sqrt_atTop.comp (tendsto_id.const_mul_atTop (by positivity)))
  refine tendsto_atTop_mono' _ ?_ hlow
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [← sub_eq_add_neg]
  exact sqrt_sub_le_critical hC hV hK h00 ht

/-- **Square-root growth at the critical rate.** `C(t) / √t → √(2 Vmax Km)`. -/
theorem tendsto_div_sqrt_critical
    (hC : ∀ t, 0 ≤ t → HasDerivAt C (Vmax - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (h00 : 0 ≤ C 0) :
    Tendsto (fun t ↦ C t / √t) atTop (𝓝 √(2 * Vmax * Km)) := by
  set a := √(2 * Vmax * Km) with ha
  have hinv : Tendsto (fun t : ℝ ↦ (√t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop
  have hlo : Tendsto (fun t ↦ a - Km * (√t)⁻¹) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.sub (hinv.const_mul Km)
  have hhi : Tendsto (fun t ↦ a + C 0 * (√t)⁻¹) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add (hinv.const_mul (C 0))
  have hsplit : ∀ t, 0 ≤ t → √(2 * Vmax * Km * t) = a * √t := fun t _ ↦
    Real.sqrt_mul (by positivity) t
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have hst : 0 < √t := Real.sqrt_pos.2 ht
    have := sqrt_sub_le_critical hC hV hK h00 ht.le
    rw [hsplit t ht.le] at this
    rw [le_div_iff₀ hst]
    have he : (a - Km * (√t)⁻¹) * √t = a * √t - Km := by field_simp
    linarith
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have hst : 0 < √t := Real.sqrt_pos.2 ht
    have := le_add_sqrt_critical hC hV hK h00 ht.le
    rw [hsplit t ht.le] at this
    rw [div_le_iff₀ hst]
    have he : (a + C 0 * (√t)⁻¹) * √t = a * √t + C 0 := by field_simp
    linarith

/-- **Sublinear growth at the critical rate.** `C(t) / t → 0`: unlike `R > Vmax`, where
`C(t) ≥ C(0) + (R - Vmax) t`, the critical accumulation is slower than every linear rate. -/
theorem tendsto_div_critical (hC : ∀ t, 0 ≤ t → HasDerivAt C (Vmax - mmRate Vmax Km (C t)) t)
    (hV : 0 < Vmax) (hK : 0 < Km) (h00 : 0 ≤ C 0) :
    Tendsto (fun t ↦ C t / t) atTop (𝓝 0) := by
  have hinv : Tendsto (fun t : ℝ ↦ (√t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop
  have := (tendsto_div_sqrt_critical hC hV hK h00).mul hinv
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [← div_eq_mul_inv, div_div, Real.mul_self_sqrt ht.le]

end Critical

end MathlibExt.Biology.Biophysics.SaturableEliminationBoundary
