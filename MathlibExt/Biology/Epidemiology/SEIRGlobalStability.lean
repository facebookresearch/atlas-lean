/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Epidemiology.SEIR
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Global stability of the SEIR endemic equilibrium via a Lyapunov function

The closed SEIR model of `MathlibExt.Biology.Epidemiology.SEIR` has no endemic equilibrium
(every solution has `E, I → 0`). An endemic state needs a supply of susceptibles, so we add
vital dynamics: births and deaths at the common per-capita rate `μ > 0`, with births entering
`S` at the constant rate `μ N`:

  `S' = μ N - β S I / N - μ S`,   `E' = β S I / N - (μ + σ) E`,
  `I' = σ E - (μ + γ) I`,          `R' = γ I - μ R`

(`IsSolution`; at `μ = 0` this is `SEIR.IsSolution`, `isSolution_zero_iff`). `R` does not enter
the first three equations, so the dynamics is that of `(S, E, I)`.

**Threshold condition.** The basic reproduction number is `R₀ = β σ / ((μ + σ) (μ + γ))`
(`R0`; at `μ = 0` it is the closed-model `β / γ`, `R0_zero`). The standing hypotheses are
`σ > 0`, `γ ≥ 0`, `μ > 0`, `N > 0` and `R₀ > 1`; then the endemic equilibrium

  `S* = N / R₀`,   `E* = μ (N - S*) / (μ + σ)`,   `I* = σ E* / (μ + γ)`

lies in the open positive orthant (`endemicS_lt`: `S* < N` exactly because `R₀ > 1`). The
disease-free case `R₀ ≤ 1` is not treated here.

**Lyapunov function** (Korobeinikov 2004), with `g(a, x) = x - a - a log (x / a)`:

  `V(S, E, I) = g(S*, S) + g(E*, E) + ((μ + σ) / σ) g(I*, I)`   (`lyapunov`).

Along solutions in the positive orthant (`IsSolution.hasDerivAt_lyapunov`),

  `V̇ = -μ (S - S*)² / S - (β S* I* / N) (S* / S + S I E* / (S* I* E) + E I* / (E* I) - 3)`,

which is `≤ 0` by three-term AM–GM (`lyapunovDeriv_nonpos`). Its zero set is
`{S = S*, E / E* = I / I*}` (`lyapunovDeriv_eq_zero_iff`), a half-line rather than the
equilibrium alone, so an invariance (LaSalle) step is needed.

**Invariance step.** `Flow.lasalle` (`MathlibExt.Dynamics.LaSalle`) needs a semiflow on the
state space; instead we carry out the step along each trajectory:

1. Forward invariance and persistence from `V` alone (`IsSolution.pos`,
   `IsSolution.exists_box_forall`): while `S, E, I > 0`, `V ≤ V(0)`, and a sublevel set of `V`
   lies in a box `[m, M]³` with `m > 0`, so the solution cannot reach the boundary.
2. `V` is nonincreasing and bounded below, hence converges; since
   `V̇ ≤ -μ (S - S*)² / S ≤ -(μ / M) (S - S*)²` and `(S - S*)²` is Lipschitz on the box,
   Barbalat's lemma gives `S → S*`.
3. `S` converges and `S'` is Lipschitz, so `S' → 0` (Barbalat), i.e. `β S I / N → μ (N - S*)`,
   so `I → I*`.
4. Likewise `I' → 0`, i.e. `σ E - (μ + γ) I → 0`, so `E → E*`.

Steps 3–4 are the statement that the largest invariant subset of `{V̇ = 0}` is the equilibrium:
on it `S ≡ S*` forces `I ≡ I*`, then `E ≡ E*`.

## Main results

* `IsSolution`, `isSolution_zero_iff`, `R0`, `R0_zero`, `endemicS`, `endemicE`, `endemicI` and
  the equilibrium identities `endemic_eq_susceptible`, `endemic_eq_exposed`,
  `endemic_eq_infected`.
* `volterra`, `lyapunov`, `lyapunovDeriv`; `lyapunov_nonneg`, `lyapunov_eq_zero_iff`.
* `IsSolution.hasDerivAt_lyapunov`, `lyapunovDeriv_nonpos`, `lyapunovDeriv_le`,
  `lyapunovDeriv_eq_zero_iff`: the Lyapunov decrease and its zero set.
* `IsSolution.pos`, `IsSolution.lyapunov_le_initial`, `IsSolution.exists_box_forall`:
  invariance of the positive orthant, monotonicity of `V`, persistence and boundedness.
* `IsSolution.tendsto_endemic`: global attractivity, `(S, E, I) → (S*, E*, I*)`.
* `endemic_lyapunovStable`, `endemic_globallyAsymptoticallyStable`: Lyapunov stability, and
  stability with global attractivity together.

## References

* A. Korobeinikov, *Lyapunov functions and global properties for SEIR and SEIS epidemic
  models*, Math. Med. Biol. 21 (2004) 75–83.
* M. Y. Li and J. S. Muldowney, *Global stability for the SEIR model in epidemiology*,
  Math. Biosci. 125 (1995) 155–164.
* H. W. Hethcote, *The mathematics of infectious diseases*, SIAM Review 42 (2000) 599–653.
* I. Barbălat, *Systèmes d'équations différentielles d'oscillations non linéaires*,
  Rev. Math. Pures Appl. 4 (1959) 267–270.
-/

@[expose] public section

open Real Filter Set
open scoped Topology

namespace MathlibExt.Biology.Epidemiology.SEIRVital

/-- `(S, E, I, R)` solves the SEIR system with vital dynamics for all times `t ≥ 0`:
births and deaths at the common per-capita rate `μ` (births into `S`, population scale `N`),
transmission rate `β`, rate `σ` of leaving the latent class and removal rate `γ`:
`S' = μ N - β S I / N - μ S`, `E' = β S I / N - (μ + σ) E`, `I' = σ E - (μ + γ) I`,
`R' = γ I - μ R`. -/
structure IsSolution (β σ γ μ N : ℝ) (S E I R : ℝ → ℝ) : Prop where
  /-- Births enter `S`; susceptibles are infected at rate `β S I / N` and die at rate `μ`. -/
  hasDerivAt_susceptible : ∀ t, 0 ≤ t → HasDerivAt S (μ * N - β * S t * I t / N - μ * S t) t
  /-- Newly infected individuals enter `E`, which they leave by progression or death. -/
  hasDerivAt_exposed : ∀ t, 0 ≤ t → HasDerivAt E (β * S t * I t / N - (μ + σ) * E t) t
  /-- Latent individuals become infectious at rate `σ`; infectives recover or die. -/
  hasDerivAt_infected : ∀ t, 0 ≤ t → HasDerivAt I (σ * E t - (μ + γ) * I t) t
  /-- Removed individuals accumulate at rate `γ I` and die at rate `μ`. -/
  hasDerivAt_removed : ∀ t, 0 ≤ t → HasDerivAt R (γ * I t - μ * R t) t

/-- **Without vital dynamics (`μ = 0`) the system is the closed SEIR model** of `SEIR.lean`. -/
theorem isSolution_zero_iff {β σ γ N : ℝ} {S E I R : ℝ → ℝ} :
    IsSolution β σ γ 0 N S E I R ↔ SEIR.IsSolution β σ γ N S E I R := by
  constructor
  · intro h
    exact ⟨fun t ht => (h.1 t ht).congr_deriv (by ring),
      fun t ht => (h.2 t ht).congr_deriv (by ring), fun t ht => (h.3 t ht).congr_deriv (by ring),
      fun t ht => (h.4 t ht).congr_deriv (by ring)⟩
  · intro h
    exact ⟨fun t ht => (h.1 t ht).congr_deriv (by ring),
      fun t ht => (h.2 t ht).congr_deriv (by ring), fun t ht => (h.3 t ht).congr_deriv (by ring),
      fun t ht => (h.4 t ht).congr_deriv (by ring)⟩

/-- The **basic reproduction number** of the SEIR model with vital dynamics,
`R₀ = β σ / ((μ + σ) (μ + γ))`: a newly infected individual survives the latent period with
probability `σ / (μ + σ)` and then infects at rate `β` for a mean time `1 / (μ + γ)`. -/
noncomputable def R0 (β σ γ μ : ℝ) : ℝ := β * σ / ((μ + σ) * (μ + γ))

/-- At `μ = 0`, `R₀` is the closed-model value `β / γ` of `SEIR.R0_eq`. -/
theorem R0_zero {β σ γ : ℝ} (hσ : σ ≠ 0) : R0 β σ γ 0 = β / γ := by
  rw [R0, zero_add, zero_add, mul_comm σ γ, mul_div_mul_right _ _ hσ]

/-- Susceptible level `S* = N / R₀` at the endemic equilibrium. -/
noncomputable def endemicS (β σ γ μ N : ℝ) : ℝ := N * (μ + σ) * (μ + γ) / (β * σ)

/-- Exposed level `E* = μ (N - S*) / (μ + σ)` at the endemic equilibrium. -/
noncomputable def endemicE (β σ γ μ N : ℝ) : ℝ := μ * (N - endemicS β σ γ μ N) / (μ + σ)

/-- Infectious level `I* = σ E* / (μ + γ)` at the endemic equilibrium. -/
noncomputable def endemicI (β σ γ μ N : ℝ) : ℝ := σ * endemicE β σ γ μ N / (μ + γ)

section Equilibrium

/-- `I' = 0` at the equilibrium: `σ E* = (μ + γ) I*` (for `μ + γ ≠ 0`). -/
theorem endemic_eq_infected {β σ γ μ N : ℝ} (hμγ : μ + γ ≠ 0) :
    σ * endemicE β σ γ μ N = (μ + γ) * endemicI β σ γ μ N := by
  rw [endemicI]
  field_simp

-- The standing hypotheses: `σ > 0`, `γ ≥ 0`, `μ > 0`, `N > 0` and the threshold `R₀ > 1`.
variable {β σ γ μ N : ℝ} (hσ : 0 < σ) (hγ : 0 ≤ γ) (hμ : 0 < μ) (hN : 0 < N)
  (hR : 1 < R0 β σ γ μ)
include hσ hγ hμ hR

theorem beta_pos : 0 < β := by
  have hd : 0 < (μ + σ) * (μ + γ) := by positivity
  have h1 : 0 < β * σ := by
    have := hR.trans_le' zero_le_one
    rw [R0] at this
    exact (div_pos_iff_of_pos_right hd).1 this
  exact pos_of_mul_pos_left h1 hσ.le

theorem endemicS_eq : endemicS β σ γ μ N = N / R0 β σ γ μ := by
  have := beta_pos hσ hγ hμ hR
  rw [endemicS, R0]
  field_simp

include hN

theorem endemicS_pos : 0 < endemicS β σ γ μ N := by
  have := beta_pos hσ hγ hμ hR
  rw [endemicS]
  positivity

/-- **The threshold**: `S* < N` exactly because `R₀ > 1`. -/
theorem endemicS_lt : endemicS β σ γ μ N < N := by
  rw [endemicS_eq hσ hγ hμ hR, div_lt_iff₀ (zero_lt_one.trans hR)]
  nlinarith

theorem endemicE_pos : 0 < endemicE β σ γ μ N := by
  have := endemicS_lt hσ hγ hμ hN hR
  rw [endemicE]
  exact div_pos (mul_pos hμ (by linarith)) (by linarith)

theorem endemicI_pos : 0 < endemicI β σ γ μ N := by
  have := endemicE_pos hσ hγ hμ hN hR
  rw [endemicI]
  exact div_pos (mul_pos hσ this) (by linarith)

/-- `β S* / N = (μ + σ) (μ + γ) / σ`. -/
theorem endemic_eq_infection : β * endemicS β σ γ μ N / N = (μ + σ) * (μ + γ) / σ := by
  have := beta_pos hσ hγ hμ hR
  rw [endemicS]
  field_simp

/-- `E' = 0` at the equilibrium: `β S* I* / N = (μ + σ) E*`. -/
theorem endemic_eq_exposed :
    β * endemicS β σ γ μ N * endemicI β σ γ μ N / N = (μ + σ) * endemicE β σ γ μ N := by
  have h := endemic_eq_infection hσ hγ hμ hN hR
  have e : β * endemicS β σ γ μ N * endemicI β σ γ μ N / N =
      β * endemicS β σ γ μ N / N * endemicI β σ γ μ N := by ring
  rw [e, h, endemicI]
  field_simp

/-- `S' = 0` at the equilibrium: `μ N = μ S* + β S* I* / N`. -/
theorem endemic_eq_susceptible : μ * N =
    μ * endemicS β σ γ μ N + β * endemicS β σ γ μ N * endemicI β σ γ μ N / N := by
  rw [endemic_eq_exposed hσ hγ hμ hN hR, endemicE]
  field_simp
  ring


end Equilibrium

/-! ### The scalar Volterra function `x - a - a log (x / a)` -/

/-- The **Volterra function** `g(a, x) = x - a - a log (x / a)`, the building block of
Goh–Volterra Lyapunov functions: `g ≥ 0` for `a, x > 0`, with equality only at `x = a`. -/
noncomputable def volterra (a x : ℝ) : ℝ := x - a - a * log (x / a)

theorem volterra_nonneg {a x : ℝ} (ha : 0 < a) (hx : 0 < x) : 0 ≤ volterra a x := by
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hx ha)) ha.le
  have e : a * (x / a - 1) = x - a := by field_simp
  rw [volterra]
  linarith

theorem volterra_eq_zero_iff {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    volterra a x = 0 ↔ x = a := by
  refine ⟨fun h => by_contra fun hne => ?_, fun h => by simp [volterra, h, div_self ha.ne']⟩
  have hne' : x / a ≠ 1 := fun h1 => hne (by rw [div_eq_one_iff_eq ha.ne'] at h1; exact h1)
  have h2 := mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos (div_pos hx ha) hne') ha
  have e : a * (x / a - 1) = x - a := by field_simp
  rw [volterra] at h
  linarith

theorem hasDerivAt_volterra {a s : ℝ} (ha : a ≠ 0) (hs : s ≠ 0) :
    HasDerivAt (volterra a) (1 - a / s) s := by
  have hl : HasDerivAt (fun x => log (x / a)) (1 / a / (s / a)) s :=
    ((hasDerivAt_id' s).div_const a).log (div_ne_zero hs ha)
  refine (((hasDerivAt_id' s).sub_const a).sub (hl.const_mul a)).congr_deriv ?_
  field_simp

/-- A sublevel bound `g(a, x) ≤ C` keeps `x` away from `0`: `x ≥ a e^{-(C + a) / a}`. -/
theorem le_of_volterra_le {a x C : ℝ} (ha : 0 < a) (hx : 0 < x) (h : volterra a x ≤ C) :
    a * exp (-(C + a) / a) ≤ x := by
  rw [volterra] at h
  have hlog : -(C + a) / a ≤ log (x / a) := by
    rw [div_le_iff₀ ha]; nlinarith
  have := (Real.le_log_iff_exp_le (div_pos hx ha)).1 hlog
  rw [le_div_iff₀ ha] at this
  linarith

/-- A sublevel bound `g(a, x) ≤ C` bounds `x` above: `x ≤ 2 (C + a)` (from `log y ≤ y / 2`). -/
theorem le_two_mul_of_volterra_le {a x C : ℝ} (ha : 0 < a) (hx : 0 < x) (h : volterra a x ≤ C) :
    x ≤ 2 * (C + a) := by
  rw [volterra] at h
  have hy : 0 < x / a / 2 := by positivity
  have h1 := Real.log_le_sub_one_of_pos hy
  rw [Real.log_div (div_pos hx ha).ne' two_ne_zero] at h1
  have h2 : log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (x := 2) two_pos (by norm_num)
    linarith
  have h3 : a * log (x / a) ≤ a * (x / a / 2 - 1 + log 2) := by
    apply mul_le_mul_of_nonneg_left _ ha.le; linarith
  have e : a * (x / a / 2 - 1 + log 2) = x / 2 - a + a * log 2 := by field_simp
  nlinarith

/-- `(x - a)² ≤ 2 M g(a, x)` for `0 < x ≤ M`, `0 < a ≤ M`: the difference has derivative
`2 (x - a) (M - x) / x`, so it is minimal (`= 0`) at `x = a`. -/
theorem sq_le_volterra {a x M : ℝ} (ha : 0 < a) (hx : 0 < x) (haM : a ≤ M) (hxM : x ≤ M) :
    (x - a) ^ 2 ≤ 2 * M * volterra a x := by
  let φ : ℝ → ℝ := fun y => 2 * M * volterra a y - (y - a) ^ 2
  have hφa : φ a = 0 := by simp [φ, volterra, div_self ha.ne']
  have hd : ∀ y, 0 < y → HasDerivAt φ (2 * (y - a) * (M - y) / y) y := by
    intro y hy
    have := ((hasDerivAt_volterra ha.ne' hy.ne').const_mul (2 * M)).sub
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

/-! ### Three-term AM–GM via `log y ≤ y - 1` -/

/-- `p + q + r ≥ 3` for positive `p, q, r` with `p q r = 1`. -/
theorem three_le_add_of_mul_eq_one {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : p * q * r = 1) : 3 ≤ p + q + r := by
  have hl : log p + log q + log r = 0 := by
    rw [← Real.log_mul hp.ne' hq.ne', ← Real.log_mul (mul_pos hp hq).ne' hr.ne', h, log_one]
  linarith [Real.log_le_sub_one_of_pos hp, Real.log_le_sub_one_of_pos hq,
    Real.log_le_sub_one_of_pos hr]

/-- Equality in `p + q + r ≥ 3` (`p q r = 1`) holds only at `p = q = r = 1`. -/
theorem eq_one_of_add_eq_three {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : p * q * r = 1) (h3 : p + q + r = 3) : p = 1 ∧ q = 1 ∧ r = 1 := by
  have hl : log p + log q + log r = 0 := by
    rw [← Real.log_mul hp.ne' hq.ne', ← Real.log_mul (mul_pos hp hq).ne' hr.ne', h, log_one]
  have key : ∀ x : ℝ, 0 < x → x - 1 - log x = 0 → x = 1 := fun x hx hx0 =>
    by_contra fun hne => by linarith [Real.log_lt_sub_one_of_pos hx hne]
  have ep := Real.log_le_sub_one_of_pos hp
  have eq := Real.log_le_sub_one_of_pos hq
  have er := Real.log_le_sub_one_of_pos hr
  exact ⟨key p hp (by linarith), key q hq (by linarith), key r hr (by linarith)⟩

/-! ### The Lyapunov function and its derivative -/

/-- The **Korobeinikov Lyapunov function** of the SEIR endemic equilibrium
`(S*, E*, I*)`:
`V(S, E, I) = g(S*, S) + g(E*, E) + ((μ + σ) / σ) g(I*, I)`, `g` the Volterra function. -/
noncomputable def lyapunov (β σ γ μ N S E I : ℝ) : ℝ :=
  volterra (endemicS β σ γ μ N) S + volterra (endemicE β σ γ μ N) E +
    (μ + σ) / σ * volterra (endemicI β σ γ μ N) I

/-- The derivative of `lyapunov` along the SEIR vector field (`IsSolution.hasDerivAt_lyapunov`):
`V̇ = -μ (S - S*)² / S - (β S* I* / N) (S* / S + S I E* / (S* I* E) + E I* / (E* I) - 3)`. -/
noncomputable def lyapunovDeriv (β σ γ μ N S E I : ℝ) : ℝ :=
  -(μ * (S - endemicS β σ γ μ N) ^ 2 / S) -
    β * endemicS β σ γ μ N * endemicI β σ γ μ N / N *
      (endemicS β σ γ μ N / S + S * I * endemicE β σ γ μ N /
        (endemicS β σ γ μ N * endemicI β σ γ μ N * E) +
        E * endemicI β σ γ μ N / (endemicE β σ γ μ N * I) - 3)

/-- The chain-rule expression for `V̇` equals `lyapunovDeriv`, by the equilibrium identities
alone (`a, e, i` stand for `S*, E*, I*`). -/
theorem lyapunov_deriv_identity {β σ γ μ N a e i S E I : ℝ} (hσ : σ ≠ 0) (hμσ : μ + σ ≠ 0)
    (hN : N ≠ 0) (ha : a ≠ 0) (he : e ≠ 0) (hi : i ≠ 0) (hS : S ≠ 0) (hE : E ≠ 0) (hI : I ≠ 0)
    (h1 : μ * N = μ * a + β * a * i / N) (h2 : β * a * i / N = (μ + σ) * e)
    (h4 : β * a / N = (μ + σ) * (μ + γ) / σ) :
    (1 - a / S) * (μ * N - β * S * I / N - μ * S) + (1 - e / E) * (β * S * I / N - (μ + σ) * E) +
      (μ + σ) / σ * ((1 - i / I) * (σ * E - (μ + γ) * I)) =
    -(μ * (S - a) ^ 2 / S) -
      β * a * i / N * (a / S + S * I * e / (a * i * E) + E * i / (e * I) - 3) := by
  rw [h1]
  have hβ : β = (μ + σ) * (μ + γ) / σ * N / a := by rw [← h4]; field_simp
  subst hβ
  have he' : e = (μ + γ) * i / σ := by
    apply mul_left_cancel₀ hμσ
    rw [← h2]
    field_simp
  subst he'
  have hμγ : μ + γ ≠ 0 := fun h0 => he (by rw [h0, zero_mul, zero_div])
  field_simp
  ring

/-- The three AM–GM terms of `lyapunovDeriv` have product `1`. -/
private theorem amgm_terms_mul {a e i S E I : ℝ} (ha : a ≠ 0) (he : e ≠ 0) (hi : i ≠ 0)
    (hS : S ≠ 0) (hE : E ≠ 0) (hI : I ≠ 0) :
    a / S * (S * I * e / (a * i * E)) * (E * i / (e * I)) = 1 := by
  field_simp

section Lyapunov

variable {β σ γ μ N : ℝ} (hσ : 0 < σ) (hγ : 0 ≤ γ) (hμ : 0 < μ) (hN : 0 < N)
  (hR : 1 < R0 β σ γ μ)
include hσ hγ hμ hN hR

/-- **`V ≥ 0`** on the positive orthant. -/
theorem lyapunov_nonneg {S E I : ℝ} (hS : 0 < S) (hE : 0 < E) (hI : 0 < I) :
    0 ≤ lyapunov β σ γ μ N S E I :=
  add_nonneg (add_nonneg (volterra_nonneg (endemicS_pos hσ hγ hμ hN hR) hS)
    (volterra_nonneg (endemicE_pos hσ hγ hμ hN hR) hE))
    (mul_nonneg (by positivity) (volterra_nonneg (endemicI_pos hσ hγ hμ hN hR) hI))

/-- **`V` vanishes only at the endemic equilibrium** on the positive orthant. -/
theorem lyapunov_eq_zero_iff {S E I : ℝ} (hS : 0 < S) (hE : 0 < E) (hI : 0 < I) :
    lyapunov β σ γ μ N S E I = 0 ↔
      S = endemicS β σ γ μ N ∧ E = endemicE β σ γ μ N ∧ I = endemicI β σ γ μ N := by
  have h1 := volterra_nonneg (endemicS_pos hσ hγ hμ hN hR) hS
  have h2 := volterra_nonneg (endemicE_pos hσ hγ hμ hN hR) hE
  have h3 := mul_nonneg (le_of_lt (by positivity : 0 < (μ + σ) / σ))
    (volterra_nonneg (endemicI_pos hσ hγ hμ hN hR) hI)
  rw [lyapunov, add_eq_zero_iff_of_nonneg (add_nonneg h1 h2) h3,
    add_eq_zero_iff_of_nonneg h1 h2, mul_eq_zero, or_iff_right (by positivity),
    volterra_eq_zero_iff (endemicS_pos hσ hγ hμ hN hR) hS,
    volterra_eq_zero_iff (endemicE_pos hσ hγ hμ hN hR) hE,
    volterra_eq_zero_iff (endemicI_pos hσ hγ hμ hN hR) hI, and_assoc]

/-- **The Lyapunov derivative is nonpositive** on the positive orthant. -/
theorem lyapunovDeriv_nonpos {S E I : ℝ} (hS : 0 < S) (hE : 0 < E) (hI : 0 < I) :
    lyapunovDeriv β σ γ μ N S E I ≤ 0 := by
  have ha := endemicS_pos hσ hγ hμ hN hR
  have he := endemicE_pos hσ hγ hμ hN hR
  have hi := endemicI_pos hσ hγ hμ hN hR
  have hβ := beta_pos hσ hγ hμ hR
  have h3 := three_le_add_of_mul_eq_one (by positivity) (by positivity) (by positivity)
    (amgm_terms_mul ha.ne' he.ne' hi.ne' hS.ne' hE.ne' hI.ne')
  have hc : 0 ≤ β * endemicS β σ γ μ N * endemicI β σ γ μ N / N := by positivity
  have hq : 0 ≤ μ * (S - endemicS β σ γ μ N) ^ 2 / S := by positivity
  rw [lyapunovDeriv]
  nlinarith [mul_nonneg hc (sub_nonneg.2 h3)]

/-- `V̇ ≤ -μ (S - S*)² / S`: the AM–GM part is nonpositive. -/
theorem lyapunovDeriv_le {S E I : ℝ} (hS : 0 < S) (hE : 0 < E) (hI : 0 < I) :
    lyapunovDeriv β σ γ μ N S E I ≤ -(μ * (S - endemicS β σ γ μ N) ^ 2 / S) := by
  have ha := endemicS_pos hσ hγ hμ hN hR
  have he := endemicE_pos hσ hγ hμ hN hR
  have hi := endemicI_pos hσ hγ hμ hN hR
  have hβ := beta_pos hσ hγ hμ hR
  have h3 := three_le_add_of_mul_eq_one (by positivity) (by positivity) (by positivity)
    (amgm_terms_mul ha.ne' he.ne' hi.ne' hS.ne' hE.ne' hI.ne')
  have hc : 0 ≤ β * endemicS β σ γ μ N * endemicI β σ γ μ N / N := by positivity
  rw [lyapunovDeriv]
  nlinarith [mul_nonneg hc (sub_nonneg.2 h3)]

/-- **The zero set of `V̇`** on the positive orthant is `{S = S*, E / E* = I / I*}`
(written `E I* = E* I`). It is a half-line through the equilibrium, not the equilibrium alone,
so `V̇ ≤ 0` does not by itself give convergence: the invariance step
(`IsSolution.tendsto_endemic`) shows that the only trajectory staying in this set is the
equilibrium. -/
theorem lyapunovDeriv_eq_zero_iff {S E I : ℝ} (hS : 0 < S) (hE : 0 < E) (hI : 0 < I) :
    lyapunovDeriv β σ γ μ N S E I = 0 ↔
      S = endemicS β σ γ μ N ∧ E * endemicI β σ γ μ N = endemicE β σ γ μ N * I := by
  have ha := endemicS_pos hσ hγ hμ hN hR
  have he := endemicE_pos hσ hγ hμ hN hR
  have hi := endemicI_pos hσ hγ hμ hN hR
  have hβ := beta_pos hσ hγ hμ hR
  set a := endemicS β σ γ μ N
  set e := endemicE β σ γ μ N
  set i := endemicI β σ γ μ N
  have hmul := amgm_terms_mul ha.ne' he.ne' hi.ne' hS.ne' hE.ne' hI.ne'
  have h3 := three_le_add_of_mul_eq_one (by positivity) (by positivity) (by positivity) hmul
  have hc : 0 < β * a * i / N := by positivity
  have hq : 0 ≤ μ * (S - a) ^ 2 / S := by positivity
  rw [lyapunovDeriv]
  constructor
  · intro h0
    have hq0 : μ * (S - a) ^ 2 / S = 0 := by nlinarith [mul_nonneg hc.le (sub_nonneg.2 h3)]
    have hg0 : a / S + S * I * e / (a * i * E) + E * i / (e * I) = 3 := by
      have : β * a * i / N * (a / S + S * I * e / (a * i * E) + E * i / (e * I) - 3) = 0 := by
        linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hc.ne'
      · linarith
    obtain ⟨-, -, hr⟩ := eq_one_of_add_eq_three (by positivity) (by positivity) (by positivity)
      hmul hg0
    refine ⟨?_, ?_⟩
    · rw [div_eq_zero_iff, mul_eq_zero, pow_eq_zero_iff two_ne_zero, sub_eq_zero] at hq0
      rcases hq0 with (h | h) | h
      · exact absurd h hμ.ne'
      · exact h
      · exact absurd h hS.ne'
    · rw [div_eq_one_iff_eq (by positivity)] at hr
      exact hr
  · rintro ⟨hSa, hEI⟩
    have hr : E * i / (e * I) = 1 := by rw [hEI, div_self (by positivity)]
    have hq1 : a * I * e / (a * i * E) = 1 := by
      rw [div_eq_one_iff_eq (by positivity)]
      linear_combination a * hEI.symm
    rw [hSa, hr, hq1, div_self ha.ne']
    ring

/-- Each Volterra term of `V` is bounded by `V` (the coefficient `(μ + σ) / σ` is `≥ 1`). -/
theorem volterra_le_lyapunov {S E I : ℝ} (hS : 0 < S) (hE : 0 < E) (hI : 0 < I) :
    volterra (endemicS β σ γ μ N) S ≤ lyapunov β σ γ μ N S E I ∧
      volterra (endemicE β σ γ μ N) E ≤ lyapunov β σ γ μ N S E I ∧
      volterra (endemicI β σ γ μ N) I ≤ lyapunov β σ γ μ N S E I := by
  have h1 := volterra_nonneg (endemicS_pos hσ hγ hμ hN hR) hS
  have h2 := volterra_nonneg (endemicE_pos hσ hγ hμ hN hR) hE
  have h3 := volterra_nonneg (endemicI_pos hσ hγ hμ hN hR) hI
  have hc : 1 ≤ (μ + σ) / σ := by rw [le_div_iff₀ hσ]; linarith
  have hc3 := le_mul_of_one_le_left h3 hc
  rw [lyapunov]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- A sublevel set of `V` in the positive orthant lies in a box `[m, M]³` with `m > 0`. -/
theorem exists_box (C : ℝ) : ∃ m M : ℝ, 0 < m ∧ ∀ S E I : ℝ, 0 < S → 0 < E → 0 < I →
    lyapunov β σ γ μ N S E I ≤ C →
      (m ≤ S ∧ S ≤ M) ∧ (m ≤ E ∧ E ≤ M) ∧ (m ≤ I ∧ I ≤ M) := by
  have ha := endemicS_pos hσ hγ hμ hN hR
  have he := endemicE_pos hσ hγ hμ hN hR
  have hi := endemicI_pos hσ hγ hμ hN hR
  set a := endemicS β σ γ μ N
  set e := endemicE β σ γ μ N
  set i := endemicI β σ γ μ N
  refine ⟨min (min (a * exp (-(C + a) / a)) (e * exp (-(C + e) / e))) (i * exp (-(C + i) / i)),
    2 * (C + a + e + i), by positivity, fun S E I hS hE hI hV => ?_⟩
  obtain ⟨vS, vE, vI⟩ := volterra_le_lyapunov hσ hγ hμ hN hR hS hE hI
  have lS := le_of_volterra_le ha hS (vS.trans hV)
  have lE := le_of_volterra_le he hE (vE.trans hV)
  have lI := le_of_volterra_le hi hI (vI.trans hV)
  have uS := le_two_mul_of_volterra_le ha hS (vS.trans hV)
  have uE := le_two_mul_of_volterra_le he hE (vE.trans hV)
  have uI := le_two_mul_of_volterra_le hi hI (vI.trans hV)
  refine ⟨⟨?_, by linarith⟩, ⟨?_, by linarith⟩, ⟨?_, by linarith⟩⟩
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans lS)
  · exact (min_le_left _ _).trans ((min_le_right _ _).trans lE)
  · exact (min_le_right _ _).trans lI

/-- `V` is continuous at the endemic equilibrium (as a function on `ℝ × ℝ × ℝ`). -/
theorem continuousAt_lyapunov :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => lyapunov β σ γ μ N p.1 p.2.1 p.2.2)
      (endemicS β σ γ μ N, endemicE β σ γ μ N, endemicI β σ γ μ N) := by
  have ha := endemicS_pos hσ hγ hμ hN hR
  have he := endemicE_pos hσ hγ hμ hN hR
  have hi := endemicI_pos hσ hγ hμ hN hR
  unfold lyapunov volterra
  fun_prop (disch := (simp only; positivity))

end Lyapunov

/-! ### Calculus lemmas on `[0, ∞)` -/

/-- A function with nonpositive derivative on `[0, t]` satisfies `f t ≤ f 0`. -/
private theorem le_of_hasDerivAt_nonpos_Icc {f f' : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hf : ∀ s ∈ Icc 0 t, HasDerivAt f (f' s) s) (hf' : ∀ s ∈ Icc 0 t, f' s ≤ 0) : f t ≤ f 0 :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hf x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hf' x (interior_subset hx)) ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht

/-- A derivative bounded by `L` on `[0, ∞)` makes the function `L`-Lipschitz there. -/
private theorem abs_sub_le_of_hasDerivAt {u u' : ℝ → ℝ} {L : ℝ}
    (hd : ∀ t, 0 ≤ t → HasDerivAt u (u' t) t) (hb : ∀ t, 0 ≤ t → |u' t| ≤ L) :
    ∀ s t, 0 ≤ s → 0 ≤ t → |u t - u s| ≤ L * |t - s| := by
  intro s t hs ht
  have := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le (f := u) (f' := u')
    (fun x hx => (hd x hx).hasDerivWithinAt)
    (fun x hx => by simpa [Real.norm_eq_abs] using hb x hx) (mem_Ici.2 hs) (mem_Ici.2 ht)
  simpa [Real.norm_eq_abs] using this

/-- **One-sided Barbalat lemma.** If `F` converges, `F' = g ≥ h` on `[0, ∞)` and `h` is
Lipschitz there, then `h < ε` eventually, for every `ε > 0`. (If `h(t) ≥ ε` at a late time,
then `h ≥ ε / 2` on `[t, t + δ]`, so `F` rises by at least `ε δ / 2` there, against the Cauchy
property of `F`.) -/
private theorem eventually_lt_of_tendsto_of_hasDerivAt {F g h : ℝ → ℝ} {c L : ℝ}
    (hF : Tendsto F atTop (𝓝 c)) (hd : ∀ t, 0 ≤ t → HasDerivAt F (g t) t) (hL : 0 ≤ L)
    (hh : ∀ s t, 0 ≤ s → 0 ≤ t → |h t - h s| ≤ L * |t - s|) (hgh : ∀ t, 0 ≤ t → h t ≤ g t)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ t in atTop, h t < ε := by
  set δ := ε / (2 * (L + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hLδ : L * δ ≤ ε / 2 := by
    rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.1 hF (ε * δ / 4) (by positivity)
  filter_upwards [eventually_ge_atTop (max T 0)] with t ht
  by_contra hcon
  push Not at hcon
  have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have hlow : ∀ u ∈ Icc t (t + δ), ε / 2 ≤ h u := by
    intro u hu
    have h1 := hh t u ht0 (by linarith [hu.1])
    rw [abs_of_nonneg (by linarith [hu.1] : 0 ≤ u - t)] at h1
    have h2 := (abs_le.1 h1).1
    nlinarith [hu.2, hu.1]
  have hder : ∀ u, 0 ≤ u → HasDerivAt (fun u => F u - ε / 2 * u) (g u - ε / 2 * 1) u :=
    fun u hu => (hd u hu).sub ((hasDerivAt_id' u).const_mul (ε / 2))
  have hmono : MonotoneOn (fun u => F u - ε / 2 * u) (Icc t (t + δ)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun u => g u - ε / 2 * 1)
      (convex_Icc _ _) (fun u hu => (hder u (by linarith [hu.1])).continuousAt.continuousWithinAt)
      (fun u hu => ?_) (fun u hu => ?_)
    · rw [interior_Icc] at hu
      exact (hder u (by linarith [hu.1])).hasDerivWithinAt
    · rw [interior_Icc] at hu
      have := hgh u (by linarith [hu.1])
      have := hlow u ⟨hu.1.le, hu.2.le⟩
      linarith
  have hinc := hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : t ≤ t + δ)
  simp only at hinc
  have d1 := hT t htT
  have d2 := hT (t + δ) (by linarith)
  rw [Real.dist_eq] at d1 d2
  have := (abs_lt.1 d1).1
  have := (abs_lt.1 d2).2
  nlinarith

/-- **Barbalat lemma.** If `F` converges and its derivative `g` on `[0, ∞)` is Lipschitz there,
then `g → 0`. -/
private theorem tendsto_zero_of_tendsto_of_hasDerivAt {F g : ℝ → ℝ} {c L : ℝ}
    (hF : Tendsto F atTop (𝓝 c)) (hd : ∀ t, 0 ≤ t → HasDerivAt F (g t) t) (hL : 0 ≤ L)
    (hg : ∀ s t, 0 ≤ s → 0 ≤ t → |g t - g s| ≤ L * |t - s|) : Tendsto g atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha =>
    eventually_lt_of_tendsto_of_hasDerivAt hF hd hL hg (fun _ _ => le_rfl) ha⟩
  have := eventually_lt_of_tendsto_of_hasDerivAt (F := fun t => -F t) (g := fun t => -g t)
    (h := fun t => -g t) hF.neg (fun t ht => (hd t ht).neg) hL
    (fun s t hs ht => by rw [show -g t - -g s = -(g t - g s) by ring, abs_neg]; exact hg s t hs ht)
    (fun _ _ => le_rfl) (neg_pos.2 ha)
  filter_upwards [this] with t ht
  linarith

namespace IsSolution

variable {β σ γ μ N : ℝ} {S E I R : ℝ → ℝ}

/-- **Derivative of the Lyapunov function along solutions.** At a time `t ≥ 0` with
`S(t), E(t), I(t) > 0`, `d/dt V(S(t), E(t), I(t)) = lyapunovDeriv (S(t), E(t), I(t))`. -/
theorem hasDerivAt_lyapunov (h : IsSolution β σ γ μ N S E I R) (hσ : 0 < σ) (hγ : 0 ≤ γ)
    (hμ : 0 < μ) (hN : 0 < N) (hR : 1 < R0 β σ γ μ) {t : ℝ} (ht : 0 ≤ t) (hSt : 0 < S t)
    (hEt : 0 < E t) (hIt : 0 < I t) :
    HasDerivAt (fun s => lyapunov β σ γ μ N (S s) (E s) (I s))
      (lyapunovDeriv β σ γ μ N (S t) (E t) (I t)) t := by
  have ha := endemicS_pos hσ hγ hμ hN hR
  have he := endemicE_pos hσ hγ hμ hN hR
  have hi := endemicI_pos hσ hγ hμ hN hR
  have dS := (hasDerivAt_volterra ha.ne' hSt.ne').comp t (h.hasDerivAt_susceptible t ht)
  have dE := (hasDerivAt_volterra he.ne' hEt.ne').comp t (h.hasDerivAt_exposed t ht)
  have dI := ((hasDerivAt_volterra hi.ne' hIt.ne').comp t (h.hasDerivAt_infected t ht)).const_mul
    ((μ + σ) / σ)
  refine ((dS.add dE).add dI).congr_deriv ?_
  rw [lyapunovDeriv]
  exact lyapunov_deriv_identity hσ.ne' (by positivity) hN.ne' ha.ne' he.ne' hi.ne' hSt.ne'
    hEt.ne' hIt.ne' (endemic_eq_susceptible hσ hγ hμ hN hR) (endemic_eq_exposed hσ hγ hμ hN hR)
    (endemic_eq_infection hσ hγ hμ hN hR)

/-- A continuous function is `≥ m` at `τ > 0` if it is `≥ m` on `(0, τ)`. -/
private theorem le_of_forall_le_Ioo {f : ℝ → ℝ} {τ m : ℝ} (hτ : 0 < τ) (hc : ContinuousAt f τ)
    (hb : ∀ s ∈ Ioo 0 τ, m ≤ f s) : m ≤ f τ :=
  ge_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds)
    (Filter.mem_of_superset (Ioo_mem_nhdsLT hτ) hb)

/-- A continuous function of the state is bounded along a trajectory confined to a box. -/
private theorem exists_bound_of_box {S E I : ℝ → ℝ} {m M : ℝ}
    (hb : ∀ t, 0 ≤ t → (m ≤ S t ∧ S t ≤ M) ∧ (m ≤ E t ∧ E t ≤ M) ∧ (m ≤ I t ∧ I t ≤ M))
    {φ : ℝ × ℝ × ℝ → ℝ} (hφ : Continuous φ) : ∃ C, ∀ t, 0 ≤ t → |φ (S t, E t, I t)| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := m) (b := M)).prod
    ((isCompact_Icc (a := m) (b := M)).prod isCompact_Icc) |>.exists_bound_of_continuousOn
      hφ.continuousOn
  refine ⟨C, fun t ht => ?_⟩
  have := hC (S t, E t, I t) ⟨(hb t ht).1, (hb t ht).2.1, (hb t ht).2.2⟩
  simpa [Real.norm_eq_abs] using this

/-- A function whose derivative is a continuous function of a boxed state is Lipschitz on
`[0, ∞)`. -/
private theorem exists_lipschitz_of_box {S E I : ℝ → ℝ} {m M : ℝ}
    (hb : ∀ t, 0 ≤ t → (m ≤ S t ∧ S t ≤ M) ∧ (m ≤ E t ∧ E t ≤ M) ∧ (m ≤ I t ∧ I t ≤ M))
    {φ : ℝ × ℝ × ℝ → ℝ} (hφ : Continuous φ) {u : ℝ → ℝ}
    (hd : ∀ t, 0 ≤ t → HasDerivAt u (φ (S t, E t, I t)) t) :
    ∃ L, 0 ≤ L ∧ ∀ s t, 0 ≤ s → 0 ≤ t → |u t - u s| ≤ L * |t - s| := by
  obtain ⟨C, hC⟩ := exists_bound_of_box hb hφ
  exact ⟨max C 0, le_max_right _ _,
    abs_sub_le_of_hasDerivAt hd fun t ht => (hC t ht).trans (le_max_left _ _)⟩

section Invariance

variable (h : IsSolution β σ γ μ N S E I R) (hσ : 0 < σ) (hγ : 0 ≤ γ) (hμ : 0 < μ) (hN : 0 < N)
  (hR : 1 < R0 β σ γ μ)
include h hσ hγ hμ hN hR

/-- `V` does not increase while the solution stays in the positive orthant. -/
theorem lyapunov_le_of_pos_on {t : ℝ} (ht : 0 ≤ t)
    (hpos : ∀ s ∈ Icc 0 t, 0 < S s ∧ 0 < E s ∧ 0 < I s) :
    lyapunov β σ γ μ N (S t) (E t) (I t) ≤ lyapunov β σ γ μ N (S 0) (E 0) (I 0) :=
  le_of_hasDerivAt_nonpos_Icc (f := fun s => lyapunov β σ γ μ N (S s) (E s) (I s)) ht
    (fun s hs => h.hasDerivAt_lyapunov hσ hγ hμ hN hR hs.1 (hpos s hs).1 (hpos s hs).2.1
      (hpos s hs).2.2)
    (fun s hs => lyapunovDeriv_nonpos hσ hγ hμ hN hR (hpos s hs).1 (hpos s hs).2.1
      (hpos s hs).2.2)

variable (hS0 : 0 < S 0) (hE0 : 0 < E 0) (hI0 : 0 < I 0)
include hS0 hE0 hI0

/-- **Forward invariance of the open positive orthant**, proved from the Lyapunov function:
while `S, E, I > 0`, `V ≤ V(0)` keeps them above a fixed `m > 0`, so they cannot reach `0`. -/
theorem pos {t : ℝ} (ht : 0 ≤ t) : 0 < S t ∧ 0 < E t ∧ 0 < I t := by
  obtain ⟨m, M, hm, hbox⟩ := exists_box hσ hγ hμ hN hR (lyapunov β σ γ μ N (S 0) (E 0) (I 0))
  have cS : ContinuousOn S (Ici 0) := fun s hs =>
    (h.hasDerivAt_susceptible s hs).continuousAt.continuousWithinAt
  have cE : ContinuousOn E (Ici 0) := fun s hs =>
    (h.hasDerivAt_exposed s hs).continuousAt.continuousWithinAt
  have cI : ContinuousOn I (Ici 0) := fun s hs =>
    (h.hasDerivAt_infected s hs).continuousAt.continuousWithinAt
  set A : Set ℝ := (Ici 0 ∩ S ⁻¹' Iic 0) ∪ (Ici 0 ∩ E ⁻¹' Iic 0) ∪ (Ici 0 ∩ I ⁻¹' Iic 0)
  have hA : IsClosed A :=
    ((cS.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic).union
      (cE.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic)).union
      (cI.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic)
  have memA : ∀ s, s ∈ A ↔ 0 ≤ s ∧ ¬ (0 < S s ∧ 0 < E s ∧ 0 < I s) := by
    intro s
    simp only [A, mem_union, mem_inter_iff, mem_Ici, mem_preimage, mem_Iic]
    constructor
    · rintro ((⟨h0, h1⟩ | ⟨h0, h1⟩) | ⟨h0, h1⟩) <;> refine ⟨h0, fun hp => ?_⟩ <;>
        linarith [hp.1, hp.2.1, hp.2.2]
    · rintro ⟨h0, hn⟩
      by_cases h1 : 0 < S s
      · by_cases h2 : 0 < E s
        · exact Or.inr ⟨h0, not_lt.1 fun h3 => hn ⟨h1, h2, h3⟩⟩
        · exact Or.inl (Or.inr ⟨h0, not_lt.1 h2⟩)
      · exact Or.inl (Or.inl ⟨h0, not_lt.1 h1⟩)
  by_contra hcon
  have hbdd : BddBelow A := ⟨0, fun s hs => ((memA s).1 hs).1⟩
  have hτA := hA.csInf_mem ⟨t, (memA t).2 ⟨ht, hcon⟩⟩ hbdd
  set τ := sInf A
  have hτ0 : 0 ≤ τ := ((memA τ).1 hτA).1
  have hbefore : ∀ s, 0 ≤ s → s < τ → 0 < S s ∧ 0 < E s ∧ 0 < I s := fun s hs hsτ => by
    by_contra hn
    exact notMem_of_lt_csInf hsτ hbdd ((memA s).2 ⟨hs, hn⟩)
  have hτpos : 0 < τ := by
    rcases hτ0.lt_or_eq with h0 | h0
    · exact h0
    · have := ((memA τ).1 hτA).2
      rw [← h0] at this
      exact absurd ⟨hS0, hE0, hI0⟩ this
  have hb : ∀ s ∈ Ioo 0 τ, (m ≤ S s ∧ S s ≤ M) ∧ (m ≤ E s ∧ E s ≤ M) ∧ (m ≤ I s ∧ I s ≤ M) := by
    intro s hs
    have hp := hbefore s hs.1.le hs.2
    exact hbox _ _ _ hp.1 hp.2.1 hp.2.2 (h.lyapunov_le_of_pos_on hσ hγ hμ hN hR hs.1.le
      fun u hu => hbefore u hu.1 (hu.2.trans_lt hs.2))
  have h1 := le_of_forall_le_Ioo hτpos (h.hasDerivAt_susceptible τ hτ0).continuousAt
    fun s hs => (hb s hs).1.1
  have h2 := le_of_forall_le_Ioo hτpos (h.hasDerivAt_exposed τ hτ0).continuousAt
    fun s hs => (hb s hs).2.1.1
  have h3 := le_of_forall_le_Ioo hτpos (h.hasDerivAt_infected τ hτ0).continuousAt
    fun s hs => (hb s hs).2.2.1
  exact ((memA τ).1 hτA).2 ⟨hm.trans_le h1, hm.trans_le h2, hm.trans_le h3⟩

/-- **`V` is nonincreasing along solutions**: `V(t) ≤ V(0)` for `t ≥ 0`. -/
theorem lyapunov_le_initial {t : ℝ} (ht : 0 ≤ t) :
    lyapunov β σ γ μ N (S t) (E t) (I t) ≤ lyapunov β σ γ μ N (S 0) (E 0) (I 0) :=
  h.lyapunov_le_of_pos_on hσ hγ hμ hN hR ht fun _ hs =>
    h.pos hσ hγ hμ hN hR hS0 hE0 hI0 hs.1

/-- **Uniform persistence and boundedness**: the solution stays in a box `[m, M]³`, `m > 0`. -/
theorem exists_box_forall :
    ∃ m M : ℝ, 0 < m ∧ ∀ t, 0 ≤ t →
      (m ≤ S t ∧ S t ≤ M) ∧ (m ≤ E t ∧ E t ≤ M) ∧ (m ≤ I t ∧ I t ≤ M) := by
  obtain ⟨m, M, hm, hbox⟩ := exists_box hσ hγ hμ hN hR (lyapunov β σ γ μ N (S 0) (E 0) (I 0))
  refine ⟨m, M, hm, fun t ht => ?_⟩
  have hp := h.pos hσ hγ hμ hN hR hS0 hE0 hI0 ht
  exact hbox _ _ _ hp.1 hp.2.1 hp.2.2 (h.lyapunov_le_initial hσ hγ hμ hN hR hS0 hE0 hI0 ht)

/-- **Global attractivity of the endemic equilibrium.** If `σ > 0`, `γ ≥ 0`, `μ > 0`, `N > 0`
and `R₀ = β σ / ((μ + σ) (μ + γ)) > 1`, every solution starting in the open positive orthant
(`S(0), E(0), I(0) > 0`) converges to `(S*, E*, I*)`.

The invariance step, done along the trajectory: `V̇ ≤ -μ (S - S*)² / S` and `V` converges, so
by Barbalat's lemma `S → S*`; then Barbalat for `S` gives `S' → 0`, i.e. `I → I*`; and for `I`
it gives `I' → 0`, i.e. `E → E*`. This is the statement that the only trajectory inside the
zero set of `V̇` (`lyapunovDeriv_eq_zero_iff`) is the equilibrium. -/
theorem tendsto_endemic :
    Tendsto (fun t => (S t, E t, I t)) atTop
      (𝓝 (endemicS β σ γ μ N, endemicE β σ γ μ N, endemicI β σ γ μ N)) := by
  obtain ⟨m, M, hm, hb⟩ := h.exists_box_forall hσ hγ hμ hN hR hS0 hE0 hI0
  have hM : 0 < M := hm.trans_le ((hb 0 le_rfl).1.1.trans (hb 0 le_rfl).1.2)
  have ha := endemicS_pos hσ hγ hμ hN hR
  have hi := endemicI_pos hσ hγ hμ hN hR
  have hβ := beta_pos hσ hγ hμ hR
  have hpos := fun t (ht : 0 ≤ t) => h.pos hσ hγ hμ hN hR hS0 hE0 hI0 ht
  set a := endemicS β σ γ μ N
  set e := endemicE β σ γ μ N
  set i := endemicI β σ γ μ N
  set W : ℝ → ℝ := fun t => lyapunov β σ γ μ N (S t) (E t) (I t)
  have hWd : ∀ t, 0 ≤ t → HasDerivAt W (lyapunovDeriv β σ γ μ N (S t) (E t) (I t)) t :=
    fun t ht => h.hasDerivAt_lyapunov hσ hγ hμ hN hR ht (hpos t ht).1 (hpos t ht).2.1
      (hpos t ht).2.2
  -- `V` converges.
  have hWanti : AntitoneOn W (Ici 0) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun x hx => (hWd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hWd x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => lyapunovDeriv_nonpos hσ hγ hμ hN hR (hpos x (interior_subset hx)).1
        (hpos x (interior_subset hx)).2.1 (hpos x (interior_subset hx)).2.2)
  have hWlim : ∃ c, Tendsto W atTop (𝓝 c) := by
    have hanti : Antitone fun t => W (max t 0) := fun s t hst =>
      hWanti (mem_Ici.2 (le_max_right _ _)) (mem_Ici.2 (le_max_right _ _))
        (max_le_max hst le_rfl)
    have hbdd : BddBelow (range fun t => W (max t 0)) := ⟨0, by
      rintro _ ⟨t, rfl⟩
      have hp := hpos (max t 0) (le_max_right _ _)
      exact lyapunov_nonneg hσ hγ hμ hN hR hp.1 hp.2.1 hp.2.2⟩
    refine ⟨_, (tendsto_atTop_ciInf hanti hbdd).congr' ?_⟩
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [max_eq_left ht]
  obtain ⟨c, hW⟩ := hWlim
  -- Step 1: `S → S*`.
  have hSa : Tendsto S atTop (𝓝 a) := by
    have hφ : Continuous fun p : ℝ × ℝ × ℝ =>
        μ * (2 * (p.1 - a) * (μ * N - β * p.1 * p.2.2 / N - μ * p.1)) / M := by fun_prop
    have hd : ∀ t, 0 ≤ t → HasDerivAt (fun t => μ * (S t - a) ^ 2 / M)
        ((fun p : ℝ × ℝ × ℝ =>
          μ * (2 * (p.1 - a) * (μ * N - β * p.1 * p.2.2 / N - μ * p.1)) / M) (S t, E t, I t))
        t := by
      intro t ht
      refine ((((h.hasDerivAt_susceptible t ht).sub_const a).pow 2).const_mul μ).div_const M
        |>.congr_deriv ?_
      dsimp only
      ring
    obtain ⟨L, hL, hLip⟩ := exists_lipschitz_of_box hb hφ hd
    have hev : ∀ ε > 0, ∀ᶠ t in atTop, μ * (S t - a) ^ 2 / M < ε := fun ε hε =>
      eventually_lt_of_tendsto_of_hasDerivAt hW.neg (fun t ht => (hWd t ht).neg) hL hLip
        (fun t ht => by
          have hp := hpos t ht
          have h1 := lyapunovDeriv_le hσ hγ hμ hN hR hp.1 hp.2.1 hp.2.2
          have h2 : μ * (S t - a) ^ 2 / M ≤ μ * (S t - a) ^ 2 / S t :=
            div_le_div_of_nonneg_left (by positivity) hp.1 (hb t ht).1.2
          linarith) hε
    have h0 : Tendsto (fun t => μ * (S t - a) ^ 2 / M) atTop (𝓝 0) :=
      tendsto_order.2 ⟨fun b hb' => Eventually.of_forall fun t => hb'.trans_le (by positivity),
        fun b hb' => hev b hb'⟩
    have hsq : Tendsto (fun t => (S t - a) ^ 2) atTop (𝓝 0) := by
      have := h0.const_mul (M / μ)
      rw [mul_zero] at this
      refine this.congr fun t => ?_
      field_simp
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have := hsq.sqrt
    simp only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] at this
    simpa [Real.norm_eq_abs] using this
  -- Step 2: `S' → 0`, hence `I → I*`.
  have hIi : Tendsto I atTop (𝓝 i) := by
    have hφ : Continuous fun p : ℝ × ℝ × ℝ =>
        -((β * (μ * N - β * p.1 * p.2.2 / N - μ * p.1) * p.2.2 +
          β * p.1 * (σ * p.2.1 - (μ + γ) * p.2.2)) / N) -
          μ * (μ * N - β * p.1 * p.2.2 / N - μ * p.1) := by fun_prop
    have hd : ∀ t, 0 ≤ t → HasDerivAt (fun t => μ * N - β * S t * I t / N - μ * S t)
        ((fun p : ℝ × ℝ × ℝ =>
          -((β * (μ * N - β * p.1 * p.2.2 / N - μ * p.1) * p.2.2 +
            β * p.1 * (σ * p.2.1 - (μ + γ) * p.2.2)) / N) -
            μ * (μ * N - β * p.1 * p.2.2 / N - μ * p.1)) (S t, E t, I t)) t := by
      intro t ht
      refine (((hasDerivAt_const t (μ * N)).sub ((((h.hasDerivAt_susceptible t ht).const_mul
        β).mul (h.hasDerivAt_infected t ht)).div_const N)).sub
        ((h.hasDerivAt_susceptible t ht).const_mul μ)).congr_deriv ?_
      dsimp only
      ring
    obtain ⟨L, hL, hLip⟩ := exists_lipschitz_of_box hb hφ hd
    have hp0 := tendsto_zero_of_tendsto_of_hasDerivAt hSa h.hasDerivAt_susceptible hL hLip
    have hlim := (((tendsto_const_nhds (x := μ * N)).sub (hSa.const_mul μ)).sub hp0).mul_const N
      |>.div (hSa.const_mul β) (by positivity)
    have heq : (μ * N - μ * a - 0) * N / (β * a) = i := by
      rw [endemic_eq_susceptible hσ hγ hμ hN hR]
      field_simp
      ring
    rw [heq] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    have := (hpos t ht).1
    change (μ * N - μ * S t - (μ * N - β * S t * I t / N - μ * S t)) * N / (β * S t) = I t
    field_simp
    ring
  -- Step 3: `I' → 0`, hence `E → E*`.
  have hEe : Tendsto E atTop (𝓝 e) := by
    have hφ : Continuous fun p : ℝ × ℝ × ℝ =>
        σ * (β * p.1 * p.2.2 / N - (μ + σ) * p.2.1) - (μ + γ) * (σ * p.2.1 - (μ + γ) * p.2.2) :=
      by fun_prop
    have hd : ∀ t, 0 ≤ t → HasDerivAt (fun t => σ * E t - (μ + γ) * I t)
        ((fun p : ℝ × ℝ × ℝ => σ * (β * p.1 * p.2.2 / N - (μ + σ) * p.2.1) -
          (μ + γ) * (σ * p.2.1 - (μ + γ) * p.2.2)) (S t, E t, I t)) t := fun t ht =>
      ((h.hasDerivAt_exposed t ht).const_mul σ).sub ((h.hasDerivAt_infected t ht).const_mul _)
    obtain ⟨L, hL, hLip⟩ := exists_lipschitz_of_box hb hφ hd
    have hq0 := tendsto_zero_of_tendsto_of_hasDerivAt hIi h.hasDerivAt_infected hL hLip
    have hlim := (hq0.add (hIi.const_mul (μ + γ))).div_const σ
    have heq : (0 + (μ + γ) * i) / σ = e := by
      rw [zero_add, ← endemic_eq_infected (by positivity)]
      field_simp
      rfl
    rw [heq] at hlim
    refine hlim.congr fun t => ?_
    field_simp
    ring
  exact hSa.prodMk_nhds (hEe.prodMk_nhds hIi)

end Invariance

end IsSolution

/-! ### Lyapunov stability and global asymptotic stability -/

section Stability

variable {β σ γ μ N : ℝ}

/-- **Lyapunov stability of the endemic equilibrium.** Under the standing hypotheses
(`σ > 0`, `γ ≥ 0`, `μ > 0`, `N > 0`, `R₀ > 1`): for every `ε > 0` there is `δ > 0` such that
every solution starting in the open positive orthant within distance `δ` of `(S*, E*, I*)`
(sup distance on `ℝ × ℝ × ℝ`) stays within distance `ε` of it for all `t ≥ 0`. -/
theorem endemic_lyapunovStable (hσ : 0 < σ) (hγ : 0 ≤ γ) (hμ : 0 < μ) (hN : 0 < N)
    (hR : 1 < R0 β σ γ μ) :
    ∀ ε > 0, ∃ δ > 0, ∀ S E I R : ℝ → ℝ, IsSolution β σ γ μ N S E I R → 0 < S 0 → 0 < E 0 →
      0 < I 0 →
      dist (S 0, E 0, I 0) (endemicS β σ γ μ N, endemicE β σ γ μ N, endemicI β σ γ μ N) < δ →
      ∀ t, 0 ≤ t →
        dist (S t, E t, I t) (endemicS β σ γ μ N, endemicE β σ γ μ N, endemicI β σ γ μ N) < ε := by
  have ha := endemicS_pos hσ hγ hμ hN hR
  have he := endemicE_pos hσ hγ hμ hN hR
  have hi := endemicI_pos hσ hγ hμ hN hR
  set a := endemicS β σ γ μ N
  set e := endemicE β σ γ μ N
  set i := endemicI β σ γ μ N
  intro ε hε
  set M₁ := 2 * (1 + a + e + i) with hM₁
  have hM₁pos : 0 < M₁ := by positivity
  set η := min 1 (ε ^ 2 / (4 * M₁)) with hη
  have hηpos : 0 < η := by positivity
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : 2 * M₁ * η < ε ^ 2 := by
    have : η ≤ ε ^ 2 / (4 * M₁) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith [sq_pos_of_pos hε]
  have hV0 : lyapunov β σ γ μ N a e i = 0 :=
    (lyapunov_eq_zero_iff hσ hγ hμ hN hR ha he hi).2 ⟨rfl, rfl, rfl⟩
  obtain ⟨δ, hδ, hcont⟩ :=
    Metric.continuousAt_iff.1 (continuousAt_lyapunov hσ hγ hμ hN hR) η hηpos
  refine ⟨δ, hδ, fun S E I R h hS0 hE0 hI0 hd t ht => ?_⟩
  have hVinit : lyapunov β σ γ μ N (S 0) (E 0) (I 0) < η := by
    have := hcont hd
    simp only at this
    rw [hV0, Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have hp := h.pos hσ hγ hμ hN hR hS0 hE0 hI0 ht
  have hVt := (h.lyapunov_le_initial hσ hγ hμ hN hR hS0 hE0 hI0 ht).trans_lt hVinit
  obtain ⟨vS, vE, vI⟩ := volterra_le_lyapunov hσ hγ hμ hN hR hp.1 hp.2.1 hp.2.2
  have key : ∀ x xs : ℝ, 0 < x → 0 < xs → xs ≤ a + e + i →
      volterra xs x ≤ lyapunov β σ γ μ N (S t) (E t) (I t) → |x - xs| < ε := by
    intro x xs hx hxs hxsM hv
    have hvη := hv.trans hVt.le
    have hxM : x ≤ M₁ := by
      have := le_two_mul_of_volterra_le hxs hx hvη
      linarith
    have := sq_le_volterra hxs hx (by linarith) hxM
    have h2 : (x - xs) ^ 2 < ε ^ 2 := by nlinarith
    exact abs_lt_of_sq_lt_sq h2 hε.le
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff,
    max_lt_iff]
  exact ⟨key _ _ hp.1 ha (by linarith) vS, key _ _ hp.2.1 he (by linarith) vE,
    key _ _ hp.2.2 hi (by linarith) vI⟩

/-- **Global asymptotic stability of the SEIR endemic equilibrium.** If `σ > 0`, `γ ≥ 0`,
`μ > 0`, `N > 0` and the threshold condition `R₀ = β σ / ((μ + σ) (μ + γ)) > 1` holds, the
endemic equilibrium `(S*, E*, I*)` is Lyapunov stable and attracts every solution starting in
the open positive orthant `S, E, I > 0`; both facts are proved from the Korobeinikov function
`lyapunov`. -/
theorem endemic_globallyAsymptoticallyStable (hσ : 0 < σ) (hγ : 0 ≤ γ) (hμ : 0 < μ)
    (hN : 0 < N) (hR : 1 < R0 β σ γ μ) :
    (∀ ε > 0, ∃ δ > 0, ∀ S E I R : ℝ → ℝ, IsSolution β σ γ μ N S E I R → 0 < S 0 → 0 < E 0 →
      0 < I 0 →
      dist (S 0, E 0, I 0) (endemicS β σ γ μ N, endemicE β σ γ μ N, endemicI β σ γ μ N) < δ →
      ∀ t, 0 ≤ t →
        dist (S t, E t, I t) (endemicS β σ γ μ N, endemicE β σ γ μ N, endemicI β σ γ μ N) < ε) ∧
    (∀ S E I R : ℝ → ℝ, IsSolution β σ γ μ N S E I R → 0 < S 0 → 0 < E 0 → 0 < I 0 →
      Tendsto (fun t => (S t, E t, I t)) atTop
        (𝓝 (endemicS β σ γ μ N, endemicE β σ γ μ N, endemicI β σ γ μ N))) :=
  ⟨endemic_lyapunovStable hσ hγ hμ hN hR, fun _ _ _ _ h hS0 hE0 hI0 =>
    h.tendsto_endemic hσ hγ hμ hN hR hS0 hE0 hI0⟩

end Stability

end MathlibExt.Biology.Epidemiology.SEIRVital
