/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Biophysics.SaturableElimination
public import Domains.Biology.Dynamics.MichaelisMenten
public import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The chemostat: steady states and the substrate equivalent

A chemostat is a well-mixed culture vessel fed with medium of substrate concentration `S_f` at
dilution rate `D`, which washes out biomass and substrate at the same rate. Biomass `X` grows on
the substrate `S` at the specific growth rate `μ(S)` and consumes `1 / y` units of substrate per
unit of biomass formed (yield `y`):

  `X' = (μ(S) - D) X`,   `S' = D (S_f - S) - μ(S) X / y`.

A state is a point `x : Fin 2 → ℝ` with biomass `x 0 = X` and substrate `x 1 = S`, so the
solutions on a set `I` of times are the integral curves `IsIntegralCurveOn x (fun _ ↦ v) I` of
the autonomous field `v = vectorField μ D Sf y`, and the norm of `Fin 2 → ℝ` is the maximum norm
on states. Monod's growth rate `μ(S) = μ_m S / (K_s + S)` has the form of the Michaelis–Menten
rate law and is `mmRate μm Ks`. For `μ_m, K_s > 0` and `D < μ_m`, the steady concentration
`S* = steadyConc μm Ks D` of saturable elimination satisfies `μ(S*) = D`, and any `S ≥ 0` with
`μ(S) = D` equals `S*`.

## Main results

* `vectorField`: the right-hand side of the balances, for any growth rate `μ : ℝ → ℝ`;
  `vectorField_washout`: the washout state `(0, S_f)` is a zero of it.
* `substrateEquivalent`: the substrate equivalent `Z = S + X / y`.
* `hasDerivWithinAt_substrateEquivalent`, `substrateEquivalent_relaxation`: along every
  solution on an interval `I ∋ 0`, `Z' = D (S_f - Z)`, so `Z(t) = S_f + (Z(0) - S_f) e^{-D t}`
  on `I`, and `Z(t) → S_f` as `t → ∞` when `D > 0` and `I ⊇ [0, ∞)`. Only the common factor
  `μ(S) X` of the two growth terms is used, not the form of `μ`.
* `interiorState`: the steady state `(X*, S*)` with `S* = D K_s / (μ_m - D)` and
  `X* = y (S_f - S*)`.
* `equilibria_and_washout_threshold`: for Monod growth with `μ_m, K_s, S_f, y > 0` and
  `D_c = μ(S_f)`: `0 < D_c < μ_m`; in the closed quadrant `X, S ≥ 0` the washout state
  `(0, S_f)` is a steady state for every `D > 0` and the only one for `D ≥ D_c`, while for
  `0 < D < D_c` the steady states are washout and `(X*, S*)`, with `0 < S* < S_f` and `X* > 0`;
  and `(X*, S*) → (0, S_f)` as `D` increases to `D_c`.

## References

* J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd
  edition, Nob Hill Publishing, Section 10.5, Equations 10.18–10.19 and the critical dilution
  rate (pp. 596–597).
-/

@[expose] public section

open Filter Set Real
open scoped Topology

namespace Domains.Biology.Dynamics.Chemostat

open MathlibExt.Biology.Dynamics.MichaelisMenten (mmRate mmRate_lt mmRate_strictMono)
open MathlibExt.Biology.Biophysics.SaturableElimination
  (steadyConc eq_steadyConc_of_mmRate_eq mmRate_steadyConc)

/-- **The chemostat vector field.** At a state `x : Fin 2 → ℝ` with biomass `X = x 0` and
substrate `S = x 1`, the chemostat with specific growth rate `μ : ℝ → ℝ`, dilution rate `D`,
feed substrate concentration `Sf` and yield `y` has the balances `X' = (μ(S) - D) X` and
`S' = D (Sf - S) - μ(S) X / y` (a quotient by `0` is `0`). Monod growth is `μ = mmRate μm Ks`,
`μ(S) = μm S / (Ks + S)`. -/
noncomputable def vectorField (μ : ℝ → ℝ) (D Sf y : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(μ (x 1) - D) * x 0, D * (Sf - x 1) - μ (x 1) * x 0 / y]

@[simp]
theorem vectorField_apply_zero (μ : ℝ → ℝ) (D Sf y : ℝ) (x : Fin 2 → ℝ) :
    vectorField μ D Sf y x 0 = (μ (x 1) - D) * x 0 := rfl

@[simp]
theorem vectorField_apply_one (μ : ℝ → ℝ) (D Sf y : ℝ) (x : Fin 2 → ℝ) :
    vectorField μ D Sf y x 1 = D * (Sf - x 1) - μ (x 1) * x 0 / y := rfl

theorem vectorField_eq_zero_iff {μ : ℝ → ℝ} {D Sf y : ℝ} {x : Fin 2 → ℝ} :
    vectorField μ D Sf y x = 0 ↔
      (μ (x 1) - D) * x 0 = 0 ∧ D * (Sf - x 1) - μ (x 1) * x 0 / y = 0 := by
  simp [funext_iff, Fin.forall_fin_two]

/-- **Washout is a steady state.** The washout state `(X, S) = (0, Sf)` is a zero of the
chemostat vector field, for every growth rate `μ : ℝ → ℝ` and all real `D`, `Sf` and `y`. -/
theorem vectorField_washout (μ : ℝ → ℝ) (D Sf y : ℝ) : vectorField μ D Sf y ![0, Sf] = 0 := by
  simp [vectorField_eq_zero_iff]

/-- **Substrate equivalent of a chemostat state.** For a state `x` with biomass `X = x 0`,
substrate `S = x 1` and yield `y`, `Z = S + X / y` (a quotient by `0` is `0`): the substrate
together with the substrate that the biomass consumed to grow. -/
noncomputable def substrateEquivalent (y : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  x 1 + x 0 / y

/-- **Rate of change of the substrate equivalent.** If a curve `x` of chemostat states has, at
time `t` and within a set `s`, the derivative given by the chemostat vector field with growth
rate `μ`, dilution rate `D`, feed `Sf` and yield `y`, then its substrate equivalent
`Z = S + X / y` has derivative `D (Sf - Z)` there. This holds for every `μ : ℝ → ℝ` and all real
`D`, `Sf` and `y` (a quotient by `0` is `0`): the growth terms `μ(S) X / y` cancel. -/
theorem hasDerivWithinAt_substrateEquivalent {μ : ℝ → ℝ} {D Sf y t : ℝ} {s : Set ℝ}
    {x : ℝ → Fin 2 → ℝ} (hx : HasDerivWithinAt x (vectorField μ D Sf y (x t)) s t) :
    HasDerivWithinAt (fun t ↦ substrateEquivalent y (x t))
      (D * (Sf - substrateEquivalent y (x t))) s t := by
  have h := hasDerivWithinAt_pi.1 hx
  have h₀ := h 0
  have h₁ := h 1
  simp only [vectorField_apply_zero, vectorField_apply_one] at h₀ h₁
  exact (h₁.fun_add (h₀.div_const y)).congr_deriv (by simp only [substrateEquivalent]; ring)

/-- **The substrate equivalent relaxes to the feed.** Let `D`, `Sf` and `y` be real and let
`μ : ℝ → ℝ` be any growth rate (a quotient by `0` is `0`). Let `I` be an interval containing `0`
and `x` a solution of the chemostat balances on `I`, that is, an integral curve on `I` of the
chemostat vector field (with derivatives within `I`). Then the substrate equivalent
`Z(t) = S(t) + X(t) / y` satisfies `Z' = D (Sf - Z)` on `I`, hence
`Z(t) = Sf + (Z(0) - Sf) e^{-D t}` for every `t ∈ I`; and if `D > 0` and `I` contains `[0, ∞)`,
then `Z(t) → Sf` as `t → ∞`. -/
theorem substrateEquivalent_relaxation {μ : ℝ → ℝ} {D Sf y : ℝ} {I : Set ℝ}
    (hI : I.OrdConnected) (h0 : 0 ∈ I) {x : ℝ → Fin 2 → ℝ}
    (hx : IsIntegralCurveOn x (fun _ ↦ vectorField μ D Sf y) I) :
    (∀ t ∈ I, HasDerivWithinAt (fun t ↦ substrateEquivalent y (x t))
      (D * (Sf - substrateEquivalent y (x t))) I t) ∧
    (∀ t ∈ I, substrateEquivalent y (x t) =
      Sf + (substrateEquivalent y (x 0) - Sf) * exp (-(D * t))) ∧
    (0 < D → Ici 0 ⊆ I → Tendsto (fun t ↦ substrateEquivalent y (x t)) atTop (𝓝 Sf)) := by
  set Z : ℝ → ℝ := fun t ↦ substrateEquivalent y (x t)
  have hZ : ∀ t ∈ I, HasDerivWithinAt Z (D * (Sf - Z t)) I t := fun t ht ↦
    hasDerivWithinAt_substrateEquivalent (hx t ht)
  -- `(Z(t) - Sf) e^{D t}` has derivative `0` on the interval `I`, so it is constant there.
  have hg : ∀ t ∈ I, HasDerivWithinAt (fun t ↦ (Z t - Sf) * exp (D * t)) 0 I t := by
    intro t ht
    have he : HasDerivWithinAt (fun t ↦ exp (D * t)) (exp (D * t) * (D * 1)) I t :=
      ((hasDerivAt_id t).const_mul D).exp.hasDerivWithinAt
    convert ((hZ t ht).sub_const Sf).mul he using 1
    ring
  have hexp : ∀ t ∈ I, Z t = Sf + (Z 0 - Sf) * exp (-(D * t)) := by
    intro t ht
    have h := hI.convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg
      (fun _ _ ↦ (norm_zero (E := ℝ)).le) h0 ht
    rw [zero_mul, norm_le_zero_iff, sub_eq_zero, mul_zero, exp_zero, mul_one] at h
    have h' := congrArg (· * exp (-(D * t))) h
    simp only [mul_assoc, ← exp_add, add_neg_cancel, exp_zero, mul_one] at h'
    linarith
  refine ⟨hZ, hexp, fun hD hsub ↦ ?_⟩
  have hdecay : Tendsto (fun t ↦ exp (-(D * t))) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hD)
  have hlim := (hdecay.const_mul (Z 0 - Sf)).const_add Sf
  rw [mul_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact (hexp t (hsub ht)).symm

/-- **Interior steady state of the chemostat.** For the Monod growth rate
`μ(S) = μm S / (Ks + S)`, dilution rate `D`, feed substrate concentration `Sf` and yield `y`, the
state `(X*, S*)` with substrate `S* = D Ks / (μm - D)` and biomass `X* = y (Sf - S*)` (a quotient
by `0` is `0`). The substrate level `S*` is the steady concentration `steadyConc μm Ks D` of
saturable elimination at infusion rate `D`: for `μm, Ks > 0` and `D < μm`, growth balances
dilution there, `μ(S*) = D`, and any `S ≥ 0` with `μ(S) = D` equals `S*`. For `μm, Ks, Sf, y > 0`
and `0 < D < μ(Sf)` the state is a steady state in the closed quadrant `X, S ≥ 0`, with
`0 < S* < Sf` and `X* > 0`. -/
noncomputable def interiorState (μm Ks D Sf y : ℝ) : Fin 2 → ℝ :=
  ![y * (Sf - steadyConc μm Ks D), steadyConc μm Ks D]

@[simp]
theorem interiorState_apply_zero (μm Ks D Sf y : ℝ) :
    interiorState μm Ks D Sf y 0 = y * (Sf - steadyConc μm Ks D) := rfl

@[simp]
theorem interiorState_apply_one (μm Ks D Sf y : ℝ) :
    interiorState μm Ks D Sf y 1 = steadyConc μm Ks D := rfl

/-- A state of `Fin 2 → ℝ` is the vector of its two coordinates. -/
private theorem eq_vec_iff {x : Fin 2 → ℝ} {a b : ℝ} : x = ![a, b] ↔ x 0 = a ∧ x 1 = b := by
  simp [funext_iff, Fin.forall_fin_two]

/-- **Chemostat equilibria and the washout threshold.** Let `μm, Ks, Sf, y > 0` and let
`μ(S) = μm S / (Ks + S)` be the Monod growth rate (`mmRate μm Ks`); put `D_c = μ(Sf)`, the
critical dilution rate. Then:

* `0 < D_c < μm`;
* for every `D > 0` the washout state `(X, S) = (0, Sf)` is a steady state of the chemostat
  balances `X' = (μ(S) - D) X`, `S' = D (Sf - S) - μ(S) X / y`;
* if `D ≥ D_c`, it is the only steady state in the closed quadrant `X ≥ 0`, `S ≥ 0`;
* if `0 < D < D_c`, the steady states in the closed quadrant are exactly the washout state and
  the interior state `(X*, S*)` with `S* = D Ks / (μm - D)` and `X* = y (Sf - S*)`, and
  `0 < S* < Sf` and `X* > 0`;
* as `D` increases to `D_c`, `(X*, S*) → (0, Sf)`, that is, `S* → Sf` and `X* → 0`. -/
theorem equilibria_and_washout_threshold {μm Ks Sf y : ℝ} (hμm : 0 < μm) (hKs : 0 < Ks)
    (hSf : 0 < Sf) (hy : 0 < y) :
    (0 < mmRate μm Ks Sf ∧ mmRate μm Ks Sf < μm) ∧
    (∀ D, 0 < D → vectorField (mmRate μm Ks) D Sf y ![0, Sf] = 0) ∧
    (∀ D, 0 < D → mmRate μm Ks Sf ≤ D →
      {x : Fin 2 → ℝ | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ vectorField (mmRate μm Ks) D Sf y x = 0} =
        {![0, Sf]}) ∧
    (∀ D, 0 < D → D < mmRate μm Ks Sf →
      {x : Fin 2 → ℝ | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ vectorField (mmRate μm Ks) D Sf y x = 0} =
          {![0, Sf], interiorState μm Ks D Sf y} ∧
        0 < interiorState μm Ks D Sf y 1 ∧ interiorState μm Ks D Sf y 1 < Sf ∧
          0 < interiorState μm Ks D Sf y 0) ∧
    Tendsto (fun D ↦ interiorState μm Ks D Sf y) (𝓝[<] mmRate μm Ks Sf) (𝓝 ![0, Sf]) := by
  set Dc := mmRate μm Ks Sf with hDc
  have hDc_pos : 0 < Dc := by simp only [hDc, mmRate]; positivity
  have hDc_lt : Dc < μm := mmRate_lt hμm hKs hSf.le
  -- `Sf` is the interior substrate level at `D = D_c`.
  have hSf_eq : Sf = steadyConc μm Ks Dc := eq_steadyConc_of_mmRate_eq hKs hDc_lt hSf.le rfl
  have hy' : y ≠ 0 := hy.ne'
  -- A steady state with `X = 0` is washout.
  have washout_of_zero : ∀ D, 0 < D → ∀ x : Fin 2 → ℝ,
      D * (Sf - x 1) - mmRate μm Ks (x 1) * x 0 / y = 0 → x 0 = 0 → x = ![0, Sf] := by
    intro D hD x h₂ hX
    rw [hX, mul_zero, zero_div, sub_zero] at h₂
    rcases mul_eq_zero.1 h₂ with h | h
    · exact absurd h hD.ne'
    · exact eq_vec_iff.2 ⟨hX, by linarith⟩
  -- On a steady state with `μ(S) = D`, the substrate balance gives `Sf - S = X / y`.
  have balance : ∀ D, 0 < D → ∀ x : Fin 2 → ℝ,
      D * (Sf - x 1) - mmRate μm Ks (x 1) * x 0 / y = 0 → mmRate μm Ks (x 1) = D →
        Sf - x 1 = x 0 / y := by
    intro D hD x h₂ hμ
    rw [hμ, mul_div_assoc, ← mul_sub, mul_eq_zero] at h₂
    rcases h₂ with h | h
    · exact absurd h hD.ne'
    · linarith
  refine ⟨⟨hDc_pos, hDc_lt⟩, fun D _ ↦ vectorField_washout _ D Sf y, ?_, ?_, ?_⟩
  · -- `D ≥ D_c`: only washout.
    intro D hD hDcD
    ext x
    simp only [mem_ofPred_eq, mem_singleton_iff, vectorField_eq_zero_iff]
    constructor
    · rintro ⟨hX, hS, h₁, h₂⟩
      rcases mul_eq_zero.1 h₁ with h | h
      · have hμ : mmRate μm Ks (x 1) = D := by linarith
        have hb := balance D hD x h₂ hμ
        have hXy : 0 ≤ x 0 / y := div_nonneg hX hy.le
        -- `S ≥ Sf`, since `μ(S) = D ≥ μ(Sf)` and `μ` is increasing on `S ≥ 0`.
        have hge : Sf ≤ x 1 := not_lt.1 fun hlt ↦ by
          have := mmRate_strictMono hμm hKs (mem_Ici.2 hS) (mem_Ici.2 hSf.le) hlt
          linarith
        have hX0 : x 0 = 0 := by
          have : x 0 / y = 0 := by linarith
          rcases div_eq_zero_iff.1 this with h | h
          · exact h
          · exact absurd h hy'
        exact washout_of_zero D hD x h₂ hX0
      · exact washout_of_zero D hD x h₂ h
    · rintro rfl
      simp [hSf.le]
  · -- `0 < D < D_c`: washout and the interior state.
    intro D hD hDDc
    have hDμ : D < μm := hDDc.trans hDc_lt
    have hμD : 0 < μm - D := sub_pos.2 hDμ
    set Ss := steadyConc μm Ks D with hSs
    have hSs_pos : 0 < Ss := div_pos (mul_pos hD hKs) hμD
    have hSs_lt : Ss < Sf := by
      rw [hSs, steadyConc, div_lt_iff₀ hμD]
      have h := hDDc
      rw [hDc, mmRate, lt_div_iff₀ (by positivity)] at h
      nlinarith
    have hXs_pos : 0 < y * (Sf - Ss) := mul_pos hy (sub_pos.2 hSs_lt)
    refine ⟨?_, hSs_pos, hSs_lt, hXs_pos⟩
    ext x
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff, vectorField_eq_zero_iff]
    constructor
    · rintro ⟨hX, hS, h₁, h₂⟩
      rcases mul_eq_zero.1 h₁ with h | h
      · right
        have hμ : mmRate μm Ks (x 1) = D := by linarith
        have hS1 : x 1 = Ss := eq_steadyConc_of_mmRate_eq hKs hDμ hS hμ
        have hb := balance D hD x h₂ hμ
        refine eq_vec_iff.2 ⟨?_, hS1⟩
        rw [← hSs, ← hS1, hb]
        field_simp
      · exact Or.inl (washout_of_zero D hD x h₂ h)
    · rintro (rfl | rfl)
      · simp [hSf.le]
      · simp only [interiorState_apply_zero, interiorState_apply_one]
        have hμ : mmRate μm Ks Ss = D := mmRate_steadyConc hμm hKs hDμ
        rw [← hSs, hμ]
        refine ⟨hXs_pos.le, hSs_pos.le, by ring, ?_⟩
        field_simp
        ring
  · -- Coalescence: the interior state tends to washout as `D` increases to `D_c`.
    have hcont : ContinuousAt (fun D ↦ steadyConc μm Ks D) Dc :=
      (continuousAt_id.mul continuousAt_const).div (continuousAt_const.sub continuousAt_id)
        (sub_ne_zero.2 hDc_lt.ne')
    have hS : Tendsto (fun D ↦ steadyConc μm Ks D) (𝓝 Dc) (𝓝 Sf) := by
      have := hcont.tendsto
      rwa [← hSf_eq] at this
    have hX : Tendsto (fun D ↦ y * (Sf - steadyConc μm Ks D)) (𝓝 Dc) (𝓝 0) := by
      have := (hS.const_sub Sf).const_mul y
      rwa [sub_self, mul_zero] at this
    refine tendsto_nhdsWithin_of_tendsto_nhds (tendsto_pi_nhds.2 fun i ↦ ?_)
    fin_cases i
    · simpa using hX
    · simpa using hS

end Domains.Biology.Dynamics.Chemostat
