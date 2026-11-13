/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Epidemiology.SIR
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The SIR system as a Mathlib ODE

`MathlibExt.Biology.Epidemiology.SIR.IsSolution β γ N S I R` states the Kermack–McKendrick
equations componentwise, with two-sided derivatives (`HasDerivAt`) at every time `t ≥ 0`. This
file connects that predicate to Mathlib's integral-curve API (`IsIntegralCurve`,
`IsIntegralCurveOn`) for the autonomous vector field `sirField β γ N` on `Fin 3 → ℝ`, with
coordinates `x 0 = S`, `x 1 = I`, `x 2 = R`.

## Endpoint conventions

`IsIntegralCurveOn α v s` asks for `HasDerivWithinAt α (v t (α t)) s t` at every `t ∈ s`. For
`s = Set.Ici 0` this is a one-sided (right) derivative at `t = 0`, while `IsSolution` asks for a
two-sided derivative there, which constrains the curve at negative times as well. Hence:

* `IsSolution.isIntegralCurveOn_Ici`: a solution gives an integral curve on `[0, ∞)`.
* `isSolution_of_isIntegralCurve`: a global integral curve gives a solution.
* `isSolution_of_isIntegralCurveOn_Ici`: an integral curve on `[0, ∞)` gives a solution
  provided the curve also has the (two-sided) derivative at `0`; at `t > 0` the set `[0, ∞)` is
  a neighbourhood of `t`, so no extra hypothesis is needed there.
* `isSolution_of_isIntegralCurveOn`: the same when the curve is an integral curve on a set `s`
  containing `[0, ∞)` that is a neighbourhood of `0`.
* `IsIntegralCurveOn.sir_hasDerivWithinAt`: on an arbitrary set `s`, the components satisfy the
  SIR equations in `HasDerivWithinAt` form.

## Local existence and uniqueness

* `sirField_contDiff`: the field is smooth (its components are polynomials).
* `exists_isIntegralCurveOn_Icc`: through every initial point `x₀ : Fin 3 → ℝ` there is an
  integral curve on some `[-ε, ε]`, `ε > 0` (Picard–Lindelöf, via Mathlib's
  `IsPicardLindelof.of_contDiffAt_one` and
  `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`).
* `exists_sir_hasDerivWithinAt_Icc`: the same, stated for the three compartments.
* `eqOn_of_isIntegralCurveOn_Icc`: two integral curves on `[a, b]` that agree at an interior
  time agree on `[a, b]` (Mathlib's `ODE_solution_unique_of_mem_Icc`, with the field Lipschitz on
  a closed ball containing both curves).

Nonnegativity, invariance of the simplex and global existence are not treated here.

An integral curve on `[0, ∞)` alone does *not* give a solution: see the tests for a curve that
agrees with a constant solution on `[0, ∞)` but has a corner at `0`.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology

namespace MathlibExt.Biology.Epidemiology.SIR

/-- The Kermack–McKendrick SIR vector field on `Fin 3 → ℝ`, with coordinates `x 0 = S`,
`x 1 = I`, `x 2 = R`: `S' = -β S I / N`, `I' = β S I / N - γ I`, `R' = γ I`. The field is
autonomous; the time argument is ignored. -/
noncomputable def sirField (β γ N : ℝ) (_t : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-(β * x 0 * x 1 / N), β * x 0 * x 1 / N - γ * x 1, γ * x 1]

/-- The curve in `Fin 3 → ℝ` obtained by packing the three compartments `S`, `I`, `R`. -/
def sirCurve (S I R : ℝ → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![S t, I t, R t]

variable {β γ N : ℝ} {S I R : ℝ → ℝ}

@[simp]
theorem sirField_apply_zero (t : ℝ) (x : Fin 3 → ℝ) :
    sirField β γ N t x 0 = -(β * x 0 * x 1 / N) := rfl

@[simp]
theorem sirField_apply_one (t : ℝ) (x : Fin 3 → ℝ) :
    sirField β γ N t x 1 = β * x 0 * x 1 / N - γ * x 1 := rfl

@[simp]
theorem sirField_apply_two (t : ℝ) (x : Fin 3 → ℝ) :
    sirField β γ N t x 2 = γ * x 1 := rfl

@[simp]
theorem sirCurve_apply_zero (t : ℝ) : sirCurve S I R t 0 = S t := rfl

@[simp]
theorem sirCurve_apply_one (t : ℝ) : sirCurve S I R t 1 = I t := rfl

@[simp]
theorem sirCurve_apply_two (t : ℝ) : sirCurve S I R t 2 = R t := rfl

/-- Every curve in `Fin 3 → ℝ` is the packing of its three components. -/
theorem sirCurve_components (α : ℝ → Fin 3 → ℝ) :
    sirCurve (α · 0) (α · 1) (α · 2) = α := by
  funext t i
  fin_cases i <;> rfl

/-- The packed curve has the field as two-sided derivative at `t` iff the three SIR equations
hold at `t` with two-sided derivatives. -/
theorem hasDerivAt_sirCurve_iff {t : ℝ} :
    HasDerivAt (sirCurve S I R) (sirField β γ N t (sirCurve S I R t)) t ↔
      HasDerivAt S (-(β * S t * I t / N)) t ∧
        HasDerivAt I (β * S t * I t / N - γ * I t) t ∧ HasDerivAt R (γ * I t) t := by
  rw [hasDerivAt_pi, Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_succ]
  simp [sirCurve, sirField]

/-- Within-set version of `hasDerivAt_sirCurve_iff`. -/
theorem hasDerivWithinAt_sirCurve_iff {s : Set ℝ} {t : ℝ} :
    HasDerivWithinAt (sirCurve S I R) (sirField β γ N t (sirCurve S I R t)) s t ↔
      HasDerivWithinAt S (-(β * S t * I t / N)) s t ∧
        HasDerivWithinAt I (β * S t * I t / N - γ * I t) s t ∧
          HasDerivWithinAt R (γ * I t) s t := by
  rw [hasDerivWithinAt_pi, Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_succ]
  simp [sirCurve, sirField]

/-- `IsSolution` is exactly the statement that the packed curve has the SIR field as its
two-sided derivative at every `t ≥ 0`. -/
theorem isSolution_iff_hasDerivAt_sirCurve :
    IsSolution β γ N S I R ↔
      ∀ t, 0 ≤ t → HasDerivAt (sirCurve S I R) (sirField β γ N t (sirCurve S I R t)) t := by
  simp only [hasDerivAt_sirCurve_iff]
  exact ⟨fun h t ht => ⟨h.1 t ht, h.2 t ht, h.3 t ht⟩,
    fun h => ⟨fun t ht => (h t ht).1, fun t ht => (h t ht).2.1, fun t ht => (h t ht).2.2⟩⟩

/-- **Forward adapter.** A solution of the SIR system packs into an integral curve of
`sirField` on `[0, ∞)`. (The two-sided derivative at `0` is weakened to a right derivative.) -/
theorem IsSolution.isIntegralCurveOn_Ici (h : IsSolution β γ N S I R) :
    IsIntegralCurveOn (sirCurve S I R) (sirField β γ N) (Ici 0) := fun t ht =>
  (isSolution_iff_hasDerivAt_sirCurve.1 h t ht).hasDerivWithinAt

/-- **Componentwise adapter on an arbitrary set.** Along an integral curve of `sirField` on `s`,
the three components satisfy the SIR equations in `HasDerivWithinAt` form at every `t ∈ s`.
No neighbourhood condition is needed; at boundary points of `s` these are one-sided
statements. -/
theorem _root_.IsIntegralCurveOn.sir_hasDerivWithinAt {α : ℝ → Fin 3 → ℝ} {s : Set ℝ}
    (h : IsIntegralCurveOn α (sirField β γ N) s) {t : ℝ} (ht : t ∈ s) :
    HasDerivWithinAt (α · 0) (-(β * α t 0 * α t 1 / N)) s t ∧
      HasDerivWithinAt (α · 1) (β * α t 0 * α t 1 / N - γ * α t 1) s t ∧
        HasDerivWithinAt (α · 2) (γ * α t 1) s t := by
  have := h t ht
  rw [← sirCurve_components α] at this
  exact hasDerivWithinAt_sirCurve_iff.1 this

/-- **Global reverse adapter.** The components of a global integral curve of `sirField` solve
the SIR system. -/
theorem isSolution_of_isIntegralCurve {α : ℝ → Fin 3 → ℝ}
    (h : IsIntegralCurve α (sirField β γ N)) :
    IsSolution β γ N (α · 0) (α · 1) (α · 2) :=
  isSolution_iff_hasDerivAt_sirCurve.2 fun t _ => by
    rw [sirCurve_components]
    exact h t

/-- **Endpoint-honest reverse adapter.** An integral curve of `sirField` on `[0, ∞)` gives a
solution of the SIR system provided it also has the two-sided derivative at `0`.

`IsIntegralCurveOn α _ (Ici 0)` only provides a right derivative at `0`, whereas `IsSolution`
asks for a two-sided derivative there; at every `t > 0` the set `Ici 0` is a neighbourhood of
`t` and the within-derivative is already two-sided. The hypothesis `h₀` cannot be dropped. -/
theorem isSolution_of_isIntegralCurveOn_Ici {α : ℝ → Fin 3 → ℝ}
    (h : IsIntegralCurveOn α (sirField β γ N) (Ici 0))
    (h₀ : HasDerivAt α (sirField β γ N 0 (α 0)) 0) :
    IsSolution β γ N (α · 0) (α · 1) (α · 2) :=
  isSolution_iff_hasDerivAt_sirCurve.2 fun t ht => by
    rw [sirCurve_components]
    rcases ht.eq_or_lt with rfl | ht
    · exact h₀
    · exact (h t ht.le).hasDerivAt (Ici_mem_nhds ht)

/-- **Reverse adapter on a neighbourhood.** An integral curve of `sirField` on a set `s ⊇ [0, ∞)`
that is a neighbourhood of `0` gives a solution of the SIR system. -/
theorem isSolution_of_isIntegralCurveOn {α : ℝ → Fin 3 → ℝ} {s : Set ℝ}
    (h : IsIntegralCurveOn α (sirField β γ N) s) (hs : Ici 0 ⊆ s) (hs₀ : s ∈ 𝓝 (0 : ℝ)) :
    IsSolution β γ N (α · 0) (α · 1) (α · 2) :=
  isSolution_of_isIntegralCurveOn_Ici (h.mono hs) ((h 0 (mem_of_mem_nhds hs₀)).hasDerivAt hs₀)

/-- Packed-curve form of `isSolution_of_isIntegralCurve`. -/
theorem isSolution_of_isIntegralCurve_sirCurve
    (h : IsIntegralCurve (sirCurve S I R) (sirField β γ N)) : IsSolution β γ N S I R :=
  isSolution_of_isIntegralCurve h

/-! ### Local existence and uniqueness -/

/-- The SIR field is smooth in the state variable: its components are polynomials in `x 0` and
`x 1`. -/
theorem sirField_contDiff {n : WithTop ℕ∞} (t : ℝ) : ContDiff ℝ n (sirField β γ N t) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · change ContDiff ℝ n fun x : Fin 3 → ℝ => -(β * x 0 * x 1 / N)
    fun_prop
  · change ContDiff ℝ n fun x : Fin 3 → ℝ => β * x 0 * x 1 / N - γ * x 1
    fun_prop
  · change ContDiff ℝ n fun x : Fin 3 → ℝ => γ * x 1
    fun_prop

/-- **Local existence (Picard–Lindelöf).** For all real parameters and every initial point
`x₀ : Fin 3 → ℝ` there are `ε > 0` and an integral curve of `sirField` on `[-ε, ε]` starting at
`x₀`. Only local existence is claimed; nonnegativity and global existence are not. -/
theorem exists_isIntegralCurveOn_Icc (β γ N : ℝ) (x₀ : Fin 3 → ℝ) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → Fin 3 → ℝ, α 0 = x₀ ∧
      IsIntegralCurveOn α (sirField β γ N) (Icc (-ε) ε) := by
  obtain ⟨ε, hε, a, r, L, K, -, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one (sirField_contDiff (β := β) (γ := γ) (N := N) (n := 1)
      0).contDiffAt (x₀ := x₀)
  obtain ⟨α, hα0, hα⟩ :=
    (hpl 0).exists_eq_forall_mem_Icc_hasDerivWithinAt (mem_closedBall_self r.2)
  have hI : Icc (0 - ε) (0 + ε) = Icc (-ε) ε := by simp
  refine ⟨ε, hε, α, hα0, fun t ht => ?_⟩
  rw [← hI] at ht ⊢
  exact hα t ht

/-- A local integral curve through `x₀` is in particular a local integral curve at `0` in the
sense of `IsIntegralCurveAt` (two-sided derivatives near `0`). -/
theorem exists_isIntegralCurveAt (β γ N : ℝ) (x₀ : Fin 3 → ℝ) :
    ∃ α : ℝ → Fin 3 → ℝ, α 0 = x₀ ∧ IsIntegralCurveAt α (sirField β γ N) 0 := by
  obtain ⟨ε, hε, α, hα0, hα⟩ := exists_isIntegralCurveOn_Icc β γ N x₀
  exact ⟨α, hα0, hα.isIntegralCurveAt (Icc_mem_nhds (neg_lt_zero.2 hε) hε)⟩

/-- **Local existence, compartment form.** For every initial state `(S₀, I₀, R₀)` there are
`ε > 0` and functions `S`, `I`, `R` with these initial values satisfying the SIR equations on
`[-ε, ε]` in `HasDerivWithinAt` form (one-sided at the endpoints `±ε`). -/
theorem exists_sir_hasDerivWithinAt_Icc (β γ N S₀ I₀ R₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ S I R : ℝ → ℝ, S 0 = S₀ ∧ I 0 = I₀ ∧ R 0 = R₀ ∧
      ∀ t ∈ Icc (-ε) ε,
        HasDerivWithinAt S (-(β * S t * I t / N)) (Icc (-ε) ε) t ∧
          HasDerivWithinAt I (β * S t * I t / N - γ * I t) (Icc (-ε) ε) t ∧
            HasDerivWithinAt R (γ * I t) (Icc (-ε) ε) t := by
  obtain ⟨ε, hε, α, hα0, hα⟩ := exists_isIntegralCurveOn_Icc β γ N ![S₀, I₀, R₀]
  exact ⟨ε, hε, (α · 0), (α · 1), (α · 2), by simp [hα0], by simp [hα0], by simp [hα0],
    fun t ht => hα.sir_hasDerivWithinAt ht⟩

/-- **Uniqueness.** Two integral curves of `sirField` on `[a, b]` that agree at a time
`t₀ ∈ (a, b)` agree on all of `[a, b]`. The field is only locally Lipschitz; it is applied on a
closed ball containing both (continuous, hence bounded) curves. -/
theorem eqOn_of_isIntegralCurveOn_Icc {α₁ α₂ : ℝ → Fin 3 → ℝ} {a b t₀ : ℝ}
    (h₁ : IsIntegralCurveOn α₁ (sirField β γ N) (Icc a b))
    (h₂ : IsIntegralCurveOn α₂ (sirField β γ N) (Icc a b))
    (ht₀ : t₀ ∈ Ioo a b) (heq : α₁ t₀ = α₂ t₀) : EqOn α₁ α₂ (Icc a b) := by
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn h₁.continuousOn
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn h₂.continuousOn
  obtain ⟨K, hK⟩ := ((sirField_contDiff (β := β) (γ := γ) (N := N) (n := 1) 0).contDiffOn
    (s := Metric.closedBall 0 (max C₁ C₂))).exists_lipschitzOnWith one_ne_zero
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  refine ODE_solution_unique_of_mem_Icc (s := fun _ => Metric.closedBall 0 (max C₁ C₂))
    (fun _ _ => hK) ht₀ h₁.continuousOn (fun t ht => ?_) (fun t ht => ?_) h₂.continuousOn
    (fun t ht => ?_) (fun t ht => ?_) heq
  · exact (h₁ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  · exact mem_closedBall_zero_iff.2 ((hC₁ t (Ioo_subset_Icc_self ht)).trans (le_max_left _ _))
  · exact (h₂ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  · exact mem_closedBall_zero_iff.2 ((hC₂ t (Ioo_subset_Icc_self ht)).trans (le_max_right _ _))

/-- **Uniqueness around `0`.** Integral curves of `sirField` on `[-ε₁, ε₁]` and `[-ε₂, ε₂]`
(`ε₁, ε₂ > 0`) with the same value at `0` agree on the common interval. -/
theorem eqOn_of_isIntegralCurveOn_Icc_zero {α₁ α₂ : ℝ → Fin 3 → ℝ} {ε₁ ε₂ : ℝ}
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (h₁ : IsIntegralCurveOn α₁ (sirField β γ N) (Icc (-ε₁) ε₁))
    (h₂ : IsIntegralCurveOn α₂ (sirField β γ N) (Icc (-ε₂) ε₂))
    (heq : α₁ 0 = α₂ 0) : EqOn α₁ α₂ (Icc (-min ε₁ ε₂) (min ε₁ ε₂)) := by
  have hε : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  refine eqOn_of_isIntegralCurveOn_Icc (h₁.mono ?_) (h₂.mono ?_) ⟨neg_lt_zero.2 hε, hε⟩ heq
  · exact Icc_subset_Icc (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  · exact Icc_subset_Icc (neg_le_neg (min_le_right _ _)) (min_le_right _ _)

end MathlibExt.Biology.Epidemiology.SIR
