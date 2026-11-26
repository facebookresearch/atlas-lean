/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Order.Compact
public import MathlibExt.Analysis.PDE.SemilinearFlow.Instability
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue

/-!
# Linearized instability for delay differential equations

The instability half of the principle of linearized stability for a retarded functional
differential equation `x'(t) = F(x_t)` (Hale and Verduyn Lunel 1993, §10.1; Diekmann et al.
1995, §VII.6). The state at time `t` is the history segment `x_t(θ) = x(t + θ)`,
`θ ∈ [-τ, 0]`, an element of the phase space `C([-τ, 0], E)` with the supremum norm.

The linearization at an equilibrium is a linear retarded equation `x'(t) = Λ(x_t)` with
`Λ : C([-τ, 0], E) →L E` (for point delays, `Λ ψ = A ψ(0) + B ψ(-τ)`). Its characteristic
equation is `Λ(e^{κ ·} v) = κ v` (for point delays, `(κ - A - e^{-κτ} B) v = 0`). The
DDE-specific step proved here is that a characteristic root `κ` with eigenvector `v` gives an
eigenvector of every time-`T` solution map of the linear equation: the segment
`θ ↦ e^{θκ} v` is mapped to `e^{Tκ}` times itself, because `t ↦ e^{tκ} v` is a solution. When
`Re κ > 0` this eigenvalue lies outside the closed unit disk, and the abstract instability
theorems of `MathlibExt.Analysis.PDE.SemilinearFlow.Instability` apply to the nonlinear
semiflow on `C([-τ, 0], E)`.

As in that module, the semiflows are explicit hypotheses; their construction (existence,
uniqueness and smooth dependence for retarded equations) is not done here:

* **Linear solution maps.** `IsTimeMap τ Λ T L` says that `L` sends the initial segment of
  every solution of `x' = Λ(x_t)` on `[0, ∞)` to its segment at time `T`. Only solutions that
  are continuous on `ℝ` and differentiable at every `t ≥ 0` (two-sided at `t = 0`) are
  constrained, so the true solution operator of the linear equation satisfies it.
* **Smoothness.** Near the equilibrium `u₀` the time-`T` map of the nonlinear semiflow is
  `u₀ + L y + O(‖y‖ᵖ)` with `p > 1` on a ball `‖y‖ ≤ ρ`. That `L` is then the time-`T` map of
  the equation linearized at `u₀` (here `IsTimeMap τ Λ T L`) is the content of the
  linearization theorem for retarded equations, not proved here.
* **Growth.** The characteristic root must dominate the growth of the linear solution maps:
  `‖Lⁿ‖ ≤ M μⁿ` with `μ < e^{p T Re κ}`, or a growth bound `‖S t‖ ≤ M e^{ωt}` with
  `ω < p Re κ`, or a spectral radius `r(L) < e^{p T Re κ}`. All hold for any remainder order
  `p > 1` when `κ` is a rightmost characteristic root and the solution operator has growth
  bound `Re κ` (spectral mapping for retarded equations, Hale and Verduyn Lunel §7.4; not
  proved here).

## Main results

* `segment`, `IsSolution`, `IsTimeMap`: history segments, solutions on `[0, ∞)` and time-`T`
  solution maps of a (possibly nonlinear) retarded equation.
* `isSolution_expSolution_iff`: `t ↦ e^{tκ} v` solves `x' = Λ(x_t)` iff `κ` is a
  characteristic root with eigenvector `v`.
* `timeMap_expSegment`: a characteristic root gives an eigenvector of every time-`T` map.
* `exists_escape_of_charRoot`, `not_lyapunovStable_of_charRoot`,
  `exists_escape_of_charRoot_semigroup`, `exists_escape_of_charRoot_spectralRadius`:
  a characteristic root with `Re κ > 0` dominating the linear growth makes the equilibrium of
  the nonlinear semiflow on `C([-τ, 0], E)` unstable.
* `isSolution_realExpSolution_iff`, `timeMap_realExpSegment`,
  `exists_escape_of_realCharRoot`, `not_lyapunovStable_of_realCharRoot`: the same for a real
  characteristic root on a real phase space `C([-τ, 0], F)`.
* `pointDelay`, `pointDelay_expSegment`, `pointDelay_realExpSegment`: the point-delay
  functional `A ψ(0) + B ψ(-τ)` and its characteristic equation.
* `exists_pos_root_of_add_pos`, `exists_timeMap_eigen_of_add_pos`: for the scalar equation
  `x'(t) = a x(t) + b x(t - τ)` with `a + b > 0` there is a real characteristic root `r > 0`,
  so every time-`T` map has the eigenvalue `e^{rT}` with a positive eigenfunction.

## Scope

Not proved here: construction of the linear and nonlinear semiflows, the derivation of the
remainder bound from smoothness of `F`, and the spectral theory of the solution operator
(that its nonzero spectrum consists of `e^{Tκ}` over characteristic roots `κ`). Those enter
only through the explicit hypotheses listed above.

Locating characteristic roots is equation-specific. For Hutchinson's delayed logistic equation,
`MathlibExt.Biology.Dynamics.DelayedLogistic.exists_charFun_eq_zero_re_pos` gives a root with
positive real part of the linearization `u'(t) = -r u(t - τ)` beyond the critical delay; the
tests show that it is a characteristic root of `pointDelay` in the sense used here.

## References

* J. K. Hale and S. M. Verduyn Lunel, *Introduction to Functional Differential Equations*,
  Applied Math. Sciences 99, Springer (1993), §1.4, §7.4, §10.1.
* O. Diekmann, S. A. van Gils, S. M. Verduyn Lunel and H.-O. Walther, *Delay Equations*,
  Applied Math. Sciences 110, Springer (1995), §VII.6.
-/

@[expose] public section

open Set

namespace MathlibExt.Analysis.ODE.DelayInstability

open MathlibExt.Analysis.PDE.SemilinearFlow

section General

variable {F : Type*}

/-- The history segment `x_t(θ) = x(t + θ)`, `θ ∈ [-τ, 0]`, of a continuous path `x`. -/
def segment [TopologicalSpace F] (τ : ℝ) (x : C(ℝ, F)) (t : ℝ) : C(Icc (-τ) 0, F) :=
  ⟨fun θ => x (t + θ), by fun_prop⟩

@[simp]
theorem segment_apply [TopologicalSpace F] (τ : ℝ) (x : C(ℝ, F)) (t : ℝ) (θ : Icc (-τ) 0) :
    segment τ x t θ = x (t + θ) := rfl

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `x` solves the retarded equation `x'(t) = Λ(x_t)` at every time `t ≥ 0` (with a
two-sided derivative at `t = 0`). The history on `[-τ, 0]` is the initial datum. -/
def IsSolution (τ : ℝ) (Λ : C(Icc (-τ) 0, F) → F) (x : C(ℝ, F)) : Prop :=
  ∀ t, 0 ≤ t → HasDerivAt x (Λ (segment τ x t)) t

/-- `L` is a time-`T` solution map of `x'(t) = Λ(x_t)`: it sends the initial segment `x_0` of
every solution to its segment `x_T` at time `T`. -/
def IsTimeMap (τ : ℝ) (Λ : C(Icc (-τ) 0, F) → F) (T : ℝ)
    (L : C(Icc (-τ) 0, F) → C(Icc (-τ) 0, F)) : Prop :=
  ∀ x, IsSolution τ Λ x → L (segment τ x 0) = segment τ x T

end General

/-- Escape from every neighbourhood contradicts Lyapunov stability. -/
theorem not_lyapunovStable_of_escape {X : Type*} [NormedAddCommGroup X] {Φ : ℝ → X → X}
    {u₀ : X} (h : ∃ ε > 0, ∀ δ > 0, ∃ x, ‖x - u₀‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖Φ t x - u₀‖) :
    ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, ‖x - u₀‖ < δ → ∀ t, 0 ≤ t → ‖Φ t x - u₀‖ < ε := by
  intro hstab
  obtain ⟨ε, hε, h⟩ := h
  obtain ⟨δ, hδ, hδε⟩ := hstab ε hε
  obtain ⟨x, hx, t, ht, hesc⟩ := h δ hδ
  exact (hδε x hx t ht).not_ge hesc

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {τ : ℝ}

/-- The exponential segment `θ ↦ e^{θκ} v` on `[-τ, 0]`. -/
noncomputable def expSegment (τ : ℝ) (κ : ℂ) (v : E) : C(Icc (-τ) 0, E) :=
  ⟨fun θ => Complex.exp ((θ : ℝ) * κ) • v, by fun_prop⟩

@[simp]
theorem expSegment_apply (κ : ℂ) (v : E) (θ : Icc (-τ) 0) :
    expSegment τ κ v θ = Complex.exp ((θ : ℝ) * κ) • v := rfl

/-- The exponential path `t ↦ e^{tκ} v`. -/
noncomputable def expSolution (κ : ℂ) (v : E) : C(ℝ, E) :=
  ⟨fun t => Complex.exp (t * κ) • v, by fun_prop⟩

@[simp]
theorem expSolution_apply (κ : ℂ) (v : E) (t : ℝ) :
    expSolution κ v t = Complex.exp (t * κ) • v := rfl

/-- The segment at time `t` of the exponential path is `exp (t κ)` times the exponential
segment. -/
theorem segment_expSolution (κ : ℂ) (v : E) (t : ℝ) :
    segment τ (expSolution κ v) t = Complex.exp (t * κ) • expSegment τ κ v := by
  ext θ
  simp only [segment_apply, expSolution_apply, ContinuousMap.smul_apply, expSegment_apply,
    smul_smul, ← Complex.exp_add, Complex.ofReal_add, add_mul]

theorem hasDerivAt_expSolution (κ : ℂ) (v : E) (t : ℝ) :
    HasDerivAt (expSolution κ v) (Complex.exp (t * κ) • κ • v) t := by
  have h : HasDerivAt (fun s : ℝ => Complex.exp (s * κ)) (Complex.exp (t * κ) * κ) t := by
    simpa using (((hasDerivAt_id (t : ℂ)).mul_const κ).cexp).comp_ofReal
  rw [smul_smul]
  exact h.smul_const v

theorem expSegment_ne_zero (hτ : 0 ≤ τ) {κ : ℂ} {v : E} (hv : v ≠ 0) :
    expSegment τ κ v ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : C(Icc (-τ) 0, E) => f ⟨0, right_mem_Icc.2 (neg_nonpos.2 hτ)⟩) h
  simp only [expSegment_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul,
    ContinuousMap.zero_apply] at h0
  exact hv h0

/-- **Characteristic equation.** The exponential path `t ↦ e^{tκ} v` solves the linear
retarded equation `x'(t) = Λ(x_t)` if and only if `Λ(e^{κ ·} v) = κ v`. -/
theorem isSolution_expSolution_iff {Λ : C(Icc (-τ) 0, E) →L[ℂ] E} {κ : ℂ} {v : E} :
    IsSolution τ Λ (expSolution κ v) ↔ Λ (expSegment τ κ v) = κ • v := by
  constructor
  · intro h
    have h0 := (hasDerivAt_expSolution κ v 0).unique (h 0 le_rfl)
    simpa [segment_expSolution] using h0.symm
  · intro hchar t _
    rw [segment_expSolution, map_smul, hchar]
    exact hasDerivAt_expSolution κ v t

/-- **A characteristic root gives an eigenvector of the solution maps.** If
`Λ(e^{κ ·} v) = κ v`, every time-`T` solution map of `x'(t) = Λ(x_t)` sends the exponential
segment `θ ↦ e^{θκ} v` to `e^{Tκ}` times itself. -/
theorem timeMap_expSegment {Λ : C(Icc (-τ) 0, E) →L[ℂ] E} {T : ℝ}
    {L : C(Icc (-τ) 0, E) → C(Icc (-τ) 0, E)} (hL : IsTimeMap τ Λ T L) {κ : ℂ} {v : E}
    (hchar : Λ (expSegment τ κ v) = κ • v) :
    L (expSegment τ κ v) = Complex.exp (T * κ) • expSegment τ κ v := by
  have h := hL _ (isSolution_expSolution_iff.2 hchar)
  rwa [segment_expSolution, segment_expSolution, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul] at h

theorem norm_exp_mul (T : ℝ) (κ : ℂ) : ‖Complex.exp (T * κ)‖ = Real.exp (T * κ.re) := by
  rw [Complex.norm_exp, Complex.re_ofReal_mul]

/-- **Linearized instability for a delay differential equation.**

`Φ t x` is the state in `C([-τ, 0], E)` at time `t` of the solution of the nonlinear equation
with initial history `x`, and `u₀` is the equilibrium. Near `u₀` the time-`T` map is
`u₀ + L y + O(‖y‖ᵖ)`, where `L` is a time-`T` solution map of the linearized equation
`x'(t) = Λ(x_t)`. If `κ` is a characteristic root (`Λ(e^{κ ·} v) = κ v`, `v ≠ 0`) with
`Re κ > 0` and `‖Lⁿ‖ ≤ M μⁿ` with `μ < e^{p T Re κ}`, then `u₀` is unstable. -/
theorem exists_escape_of_charRoot {Λ : C(Icc (-τ) 0, E) →L[ℂ] E}
    {L : C(Icc (-τ) 0, E) →L[ℂ] C(Icc (-τ) 0, E)}
    {Φ : ℝ → C(Icc (-τ) 0, E) → C(Icc (-τ) 0, E)} {u₀ : C(Icc (-τ) 0, E)}
    {T ρ C p M μ : ℝ} {κ : ℂ} {v : E}
    (hτ : 0 ≤ τ) (hT : 0 < T) (hρ : 0 < ρ) (hC : 0 ≤ C) (hp : 1 < p)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hstep : ∀ (n : ℕ) x, (∀ k ≤ n, ‖Φ (k * T) x - u₀‖ ≤ ρ) →
      Φ ((n + 1) * T) x = Φ T (Φ (n * T) x))
    (hrem : ∀ y, ‖y‖ ≤ ρ → ‖Φ T (u₀ + y) - u₀ - L y‖ ≤ C * ‖y‖ ^ p)
    (hL : IsTimeMap τ Λ T L)
    (hv : v ≠ 0) (hchar : Λ (expSegment τ κ v) = κ • v) (hκ : 0 < κ.re)
    (hμ0 : 0 ≤ μ) (hμ : μ < Real.exp (p * T * κ.re)) (hM : ∀ n : ℕ, ‖L ^ n‖ ≤ M * μ ^ n) :
    ∃ ε > 0, ∀ δ > 0, ∃ x, ‖x - u₀‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖Φ t x - u₀‖ := by
  refine Instability.exists_escape_of_timeMap hT.le hρ hC hp hΦ0 hstep hrem
    (expSegment_ne_zero hτ hv) (timeMap_expSegment hL hchar) ?_ hμ0 ?_ hM
  · rw [norm_exp_mul]; exact Real.one_lt_exp_iff.2 (mul_pos hT hκ)
  · rw [norm_exp_mul, ← Real.exp_mul]; convert hμ using 2; ring

/-- Lyapunov form of `exists_escape_of_charRoot`: the equilibrium `u₀` of the delay equation
is not Lyapunov stable in `C([-τ, 0], E)`. -/
theorem not_lyapunovStable_of_charRoot {Λ : C(Icc (-τ) 0, E) →L[ℂ] E}
    {L : C(Icc (-τ) 0, E) →L[ℂ] C(Icc (-τ) 0, E)}
    {Φ : ℝ → C(Icc (-τ) 0, E) → C(Icc (-τ) 0, E)} {u₀ : C(Icc (-τ) 0, E)}
    {T ρ C p M μ : ℝ} {κ : ℂ} {v : E}
    (hτ : 0 ≤ τ) (hT : 0 < T) (hρ : 0 < ρ) (hC : 0 ≤ C) (hp : 1 < p)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hstep : ∀ (n : ℕ) x, (∀ k ≤ n, ‖Φ (k * T) x - u₀‖ ≤ ρ) →
      Φ ((n + 1) * T) x = Φ T (Φ (n * T) x))
    (hrem : ∀ y, ‖y‖ ≤ ρ → ‖Φ T (u₀ + y) - u₀ - L y‖ ≤ C * ‖y‖ ^ p)
    (hL : IsTimeMap τ Λ T L)
    (hv : v ≠ 0) (hchar : Λ (expSegment τ κ v) = κ • v) (hκ : 0 < κ.re)
    (hμ0 : 0 ≤ μ) (hμ : μ < Real.exp (p * T * κ.re)) (hM : ∀ n : ℕ, ‖L ^ n‖ ≤ M * μ ^ n) :
    ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, ‖x - u₀‖ < δ → ∀ t, 0 ≤ t → ‖Φ t x - u₀‖ < ε :=
  not_lyapunovStable_of_escape <| exists_escape_of_charRoot hτ hT hρ hC hp hΦ0 hstep hrem hL
    hv hchar hκ hμ0 hμ hM

/-- **Linearized instability for a delay differential equation, semigroup form.** `S` is the
solution semigroup of the linearized equation `x'(t) = Λ(x_t)` with growth bound
`‖S t‖ ≤ M e^{ωt}`; only `S T` is required to be a time-`T` solution map. A characteristic
root `κ` with `Re κ > 0` and `ω < p Re κ` makes the equilibrium unstable. -/
theorem exists_escape_of_charRoot_semigroup {Λ : C(Icc (-τ) 0, E) →L[ℂ] E}
    {S : ℝ → C(Icc (-τ) 0, E) →L[ℂ] C(Icc (-τ) 0, E)}
    {Φ : ℝ → C(Icc (-τ) 0, E) → C(Icc (-τ) 0, E)} {u₀ : C(Icc (-τ) 0, E)}
    {T ρ C p M ω : ℝ} {κ : ℂ} {v : E}
    (hτ : 0 ≤ τ) (hT : 0 < T) (hρ : 0 < ρ) (hC : 0 ≤ C) (hp : 1 < p)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hstep : ∀ (n : ℕ) x, (∀ k ≤ n, ‖Φ (k * T) x - u₀‖ ≤ ρ) →
      Φ ((n + 1) * T) x = Φ T (Φ (n * T) x))
    (hrem : ∀ y, ‖y‖ ≤ ρ → ‖Φ T (u₀ + y) - u₀ - S T y‖ ≤ C * ‖y‖ ^ p)
    (hS0 : S 0 = 1) (hSadd : ∀ s t, 0 ≤ s → 0 ≤ t → S (s + t) = S s * S t)
    (hSbound : ∀ t, 0 ≤ t → ‖S t‖ ≤ M * Real.exp (ω * t))
    (hST : IsTimeMap τ Λ T (S T))
    (hv : v ≠ 0) (hchar : Λ (expSegment τ κ v) = κ • v) (hκ : 0 < κ.re)
    (hω : ω < p * κ.re) :
    ∃ ε > 0, ∀ δ > 0, ∃ x, ‖x - u₀‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖Φ t x - u₀‖ :=
  Instability.exists_escape_of_semigroup hT hρ hC hp hΦ0 hstep hrem hS0 hSadd hSbound
    (expSegment_ne_zero hτ hv) (timeMap_expSegment hST hchar) hκ hω

/-- **Linearized instability for a delay differential equation, spectral-radius form.** For a
complete `E`, a characteristic root `κ` with `Re κ > 0` and spectral radius
`r(L) < e^{p T Re κ}` of the time-`T` solution map makes the equilibrium unstable. When `κ` is
a rightmost root and `r(L) = e^{T Re κ}`, this holds for every `p > 1`. -/
theorem exists_escape_of_charRoot_spectralRadius [CompleteSpace E]
    {Λ : C(Icc (-τ) 0, E) →L[ℂ] E} {L : C(Icc (-τ) 0, E) →L[ℂ] C(Icc (-τ) 0, E)}
    {Φ : ℝ → C(Icc (-τ) 0, E) → C(Icc (-τ) 0, E)} {u₀ : C(Icc (-τ) 0, E)}
    {T ρ C p : ℝ} {κ : ℂ} {v : E}
    (hτ : 0 ≤ τ) (hT : 0 < T) (hρ : 0 < ρ) (hC : 0 ≤ C) (hp : 1 < p)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hstep : ∀ (n : ℕ) x, (∀ k ≤ n, ‖Φ (k * T) x - u₀‖ ≤ ρ) →
      Φ ((n + 1) * T) x = Φ T (Φ (n * T) x))
    (hrem : ∀ y, ‖y‖ ≤ ρ → ‖Φ T (u₀ + y) - u₀ - L y‖ ≤ C * ‖y‖ ^ p)
    (hL : IsTimeMap τ Λ T L)
    (hv : v ≠ 0) (hchar : Λ (expSegment τ κ v) = κ • v) (hκ : 0 < κ.re)
    (hr : spectralRadius ℂ L < ENNReal.ofReal (Real.exp (p * T * κ.re))) :
    ∃ ε > 0, ∀ δ > 0, ∃ x, ‖x - u₀‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖Φ t x - u₀‖ := by
  refine Instability.flow_escape_of_map_escape hT.le hΦ0 hstep ?_
  refine Instability.exists_escape_of_spectralRadius hρ hC hp hrem
    (expSegment_ne_zero hτ hv) (timeMap_expSegment hL hchar) ?_ ?_
  · rw [norm_exp_mul]; exact Real.one_lt_exp_iff.2 (mul_pos hT hκ)
  · rw [norm_exp_mul, ← Real.exp_mul]; convert hr using 3; ring

end Complex

section Real

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {τ : ℝ}

/-- The real exponential segment `θ ↦ e^{θr} v` on `[-τ, 0]`. -/
noncomputable def realExpSegment (τ r : ℝ) (v : F) : C(Icc (-τ) 0, F) :=
  ⟨fun θ => Real.exp ((θ : ℝ) * r) • v, by fun_prop⟩

@[simp]
theorem realExpSegment_apply (r : ℝ) (v : F) (θ : Icc (-τ) 0) :
    realExpSegment τ r v θ = Real.exp ((θ : ℝ) * r) • v := rfl

/-- The real exponential path `t ↦ e^{tr} v`. -/
noncomputable def realExpSolution (r : ℝ) (v : F) : C(ℝ, F) :=
  ⟨fun t => Real.exp (t * r) • v, by fun_prop⟩

@[simp]
theorem realExpSolution_apply (r : ℝ) (v : F) (t : ℝ) :
    realExpSolution r v t = Real.exp (t * r) • v := rfl

theorem segment_realExpSolution (r : ℝ) (v : F) (t : ℝ) :
    segment τ (realExpSolution r v) t = Real.exp (t * r) • realExpSegment τ r v := by
  ext θ
  simp only [segment_apply, realExpSolution_apply, ContinuousMap.smul_apply,
    realExpSegment_apply, smul_smul, ← Real.exp_add, add_mul]

theorem hasDerivAt_realExpSolution (r : ℝ) (v : F) (t : ℝ) :
    HasDerivAt (realExpSolution r v) (Real.exp (t * r) • r • v) t := by
  have h : HasDerivAt (fun s : ℝ => Real.exp (s * r)) (Real.exp (t * r) * r) t := by
    simpa using ((hasDerivAt_id t).mul_const r).exp
  rw [smul_smul]
  exact h.smul_const v

theorem realExpSegment_ne_zero (hτ : 0 ≤ τ) {r : ℝ} {v : F} (hv : v ≠ 0) :
    realExpSegment τ r v ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : C(Icc (-τ) 0, F) => f ⟨0, right_mem_Icc.2 (neg_nonpos.2 hτ)⟩) h
  simp only [realExpSegment_apply, zero_mul, Real.exp_zero, one_smul,
    ContinuousMap.zero_apply] at h0
  exact hv h0

/-- **Real characteristic equation.** `t ↦ e^{tr} v` solves `x'(t) = Λ(x_t)` if and only if
`Λ(e^{r ·} v) = r v`. -/
theorem isSolution_realExpSolution_iff {Λ : C(Icc (-τ) 0, F) →L[ℝ] F} {r : ℝ} {v : F} :
    IsSolution τ Λ (realExpSolution r v) ↔ Λ (realExpSegment τ r v) = r • v := by
  constructor
  · intro h
    have h0 := (hasDerivAt_realExpSolution r v 0).unique (h 0 le_rfl)
    simpa [segment_realExpSolution] using h0.symm
  · intro hchar t _
    rw [segment_realExpSolution, map_smul, hchar]
    exact hasDerivAt_realExpSolution r v t

/-- A real characteristic root `r` gives the eigenvalue `e^{Tr}` of every time-`T` solution
map, with eigenvector the exponential segment `θ ↦ e^{θr} v`. -/
theorem timeMap_realExpSegment {Λ : C(Icc (-τ) 0, F) →L[ℝ] F} {T : ℝ}
    {L : C(Icc (-τ) 0, F) → C(Icc (-τ) 0, F)} (hL : IsTimeMap τ Λ T L) {r : ℝ} {v : F}
    (hchar : Λ (realExpSegment τ r v) = r • v) :
    L (realExpSegment τ r v) = Real.exp (T * r) • realExpSegment τ r v := by
  have h := hL _ (isSolution_realExpSolution_iff.2 hchar)
  rwa [segment_realExpSolution, segment_realExpSolution, zero_mul, Real.exp_zero,
    one_smul] at h

/-- **Linearized instability for a delay differential equation, real root.** The real
counterpart of `exists_escape_of_charRoot` on the real phase space `C([-τ, 0], F)`: a real
characteristic root `r > 0` with `‖Lⁿ‖ ≤ M μⁿ`, `μ < e^{p T r}` makes the equilibrium unstable. -/
theorem exists_escape_of_realCharRoot {Λ : C(Icc (-τ) 0, F) →L[ℝ] F}
    {L : C(Icc (-τ) 0, F) →L[ℝ] C(Icc (-τ) 0, F)}
    {Φ : ℝ → C(Icc (-τ) 0, F) → C(Icc (-τ) 0, F)} {u₀ : C(Icc (-τ) 0, F)}
    {T ρ C p M μ r : ℝ} {v : F}
    (hτ : 0 ≤ τ) (hT : 0 < T) (hρ : 0 < ρ) (hC : 0 ≤ C) (hp : 1 < p)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hstep : ∀ (n : ℕ) x, (∀ k ≤ n, ‖Φ (k * T) x - u₀‖ ≤ ρ) →
      Φ ((n + 1) * T) x = Φ T (Φ (n * T) x))
    (hrem : ∀ y, ‖y‖ ≤ ρ → ‖Φ T (u₀ + y) - u₀ - L y‖ ≤ C * ‖y‖ ^ p)
    (hL : IsTimeMap τ Λ T L)
    (hv : v ≠ 0) (hchar : Λ (realExpSegment τ r v) = r • v) (hr : 0 < r)
    (hμ0 : 0 ≤ μ) (hμ : μ < Real.exp (p * T * r)) (hM : ∀ n : ℕ, ‖L ^ n‖ ≤ M * μ ^ n) :
    ∃ ε > 0, ∀ δ > 0, ∃ x, ‖x - u₀‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖Φ t x - u₀‖ := by
  have hnorm : ‖Real.exp (T * r)‖ = Real.exp (T * r) :=
    Real.norm_of_nonneg (Real.exp_pos _).le
  refine Instability.exists_escape_of_timeMap hT.le hρ hC hp hΦ0 hstep hrem
    (realExpSegment_ne_zero hτ hv) (timeMap_realExpSegment hL hchar) ?_ hμ0 ?_ hM
  · rw [hnorm]; exact Real.one_lt_exp_iff.2 (mul_pos hT hr)
  · rw [hnorm, ← Real.exp_mul]; convert hμ using 2; ring

/-- Lyapunov form of `exists_escape_of_realCharRoot`. -/
theorem not_lyapunovStable_of_realCharRoot {Λ : C(Icc (-τ) 0, F) →L[ℝ] F}
    {L : C(Icc (-τ) 0, F) →L[ℝ] C(Icc (-τ) 0, F)}
    {Φ : ℝ → C(Icc (-τ) 0, F) → C(Icc (-τ) 0, F)} {u₀ : C(Icc (-τ) 0, F)}
    {T ρ C p M μ r : ℝ} {v : F}
    (hτ : 0 ≤ τ) (hT : 0 < T) (hρ : 0 < ρ) (hC : 0 ≤ C) (hp : 1 < p)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hstep : ∀ (n : ℕ) x, (∀ k ≤ n, ‖Φ (k * T) x - u₀‖ ≤ ρ) →
      Φ ((n + 1) * T) x = Φ T (Φ (n * T) x))
    (hrem : ∀ y, ‖y‖ ≤ ρ → ‖Φ T (u₀ + y) - u₀ - L y‖ ≤ C * ‖y‖ ^ p)
    (hL : IsTimeMap τ Λ T L)
    (hv : v ≠ 0) (hchar : Λ (realExpSegment τ r v) = r • v) (hr : 0 < r)
    (hμ0 : 0 ≤ μ) (hμ : μ < Real.exp (p * T * r)) (hM : ∀ n : ℕ, ‖L ^ n‖ ≤ M * μ ^ n) :
    ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, ‖x - u₀‖ < δ → ∀ t, 0 ≤ t → ‖Φ t x - u₀‖ < ε :=
  not_lyapunovStable_of_escape <| exists_escape_of_realCharRoot hτ hT hρ hC hp hΦ0 hstep hrem
    hL hv hchar hr hμ0 hμ hM

end Real

section PointDelay

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {τ : ℝ}

/-- The point-delay functional `ψ ↦ A ψ(0) + B ψ(-τ)`: `x'(t) = Λ(x_t)` with this `Λ` is
`x'(t) = A x(t) + B x(t - τ)`. -/
noncomputable def pointDelay (hτ : 0 ≤ τ) (A B : F →L[𝕜] F) : C(Icc (-τ) 0, F) →L[𝕜] F :=
  A.comp (ContinuousMap.evalCLM (R := 𝕜) ⟨0, right_mem_Icc.2 (neg_nonpos.2 hτ)⟩) +
    B.comp (ContinuousMap.evalCLM (R := 𝕜) ⟨-τ, left_mem_Icc.2 (neg_nonpos.2 hτ)⟩)

theorem pointDelay_apply (hτ : 0 ≤ τ) (A B : F →L[𝕜] F) (ψ : C(Icc (-τ) 0, F)) :
    pointDelay hτ A B ψ = A (ψ ⟨0, right_mem_Icc.2 (neg_nonpos.2 hτ)⟩) +
      B (ψ ⟨-τ, left_mem_Icc.2 (neg_nonpos.2 hτ)⟩) := rfl

end PointDelay

/-- The characteristic equation of `x'(t) = A x(t) + B x(t - τ)` at `e^{κ ·} v` is
`A v + e^{-τκ} B v = κ v`. -/
theorem pointDelay_expSegment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {τ : ℝ}
    (hτ : 0 ≤ τ) (A B : E →L[ℂ] E) (κ : ℂ) (v : E) :
    pointDelay hτ A B (expSegment τ κ v) = A v + Complex.exp (-τ * κ) • B v := by
  simp [pointDelay_apply]

/-- The real characteristic equation of `x'(t) = A x(t) + B x(t - τ)` at `e^{r ·} v` is
`A v + e^{-τr} B v = r v`. -/
theorem pointDelay_realExpSegment {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {τ : ℝ} (hτ : 0 ≤ τ) (A B : F →L[ℝ] F) (r : ℝ) (v : F) :
    pointDelay hτ A B (realExpSegment τ r v) = A v + Real.exp (-τ * r) • B v := by
  simp [pointDelay_apply]

section Scalar

/-- **Positive real characteristic root of a scalar delay equation.** If `a + b > 0` and
`τ ≥ 0`, the characteristic equation `r = a + b e^{-τr}` of `x'(t) = a x(t) + b x(t - τ)` has
a root `r > 0`. -/
theorem exists_pos_root_of_add_pos {a b τ : ℝ} (hτ : 0 ≤ τ) (hab : 0 < a + b) :
    ∃ r > 0, r = a + b * Real.exp (-τ * r) := by
  set R := |a| + |b| + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hgR : 0 ≤ R - a - b * Real.exp (-τ * R) := by
    have he : Real.exp (-τ * R) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hb : b * Real.exp (-τ * R) ≤ |b| :=
      calc b * Real.exp (-τ * R) ≤ |b * Real.exp (-τ * R)| := le_abs_self _
        _ = |b| * Real.exp (-τ * R) := by rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        _ ≤ |b| := mul_le_of_le_one_right (abs_nonneg b) he
    linarith [le_abs_self a]
  obtain ⟨r, ⟨hr0, -⟩, hr⟩ := intermediate_value_Icc hR0
    (f := fun r => r - a - b * Real.exp (-τ * r)) (by fun_prop)
    ⟨by simp only [mul_zero, Real.exp_zero]; linarith, hgR⟩
  simp only at hr
  refine ⟨r, lt_of_le_of_ne hr0 ?_, by linarith⟩
  rintro rfl
  simp only [mul_zero, Real.exp_zero] at hr
  linarith

/-- **Linear instability of a scalar delay equation with `a + b > 0`.** There is `r > 0`
such that every time-`T` solution map of `x'(t) = a x(t) + b x(t - τ)` on `C([-τ, 0], ℝ)` has
the eigenvalue `e^{Tr}` with the positive eigenfunction `θ ↦ e^{θr}`. -/
theorem exists_timeMap_eigen_of_add_pos {a b τ : ℝ} (hτ : 0 ≤ τ) (hab : 0 < a + b) :
    ∃ r > 0, ∀ (T : ℝ) (L : C(Icc (-τ) 0, ℝ) → C(Icc (-τ) 0, ℝ)),
      IsTimeMap τ (pointDelay hτ (a • ContinuousLinearMap.id ℝ ℝ)
        (b • ContinuousLinearMap.id ℝ ℝ)) T L →
        L (realExpSegment τ r 1) = Real.exp (T * r) • realExpSegment τ r 1 := by
  obtain ⟨r, hr, hroot⟩ := exists_pos_root_of_add_pos hτ hab
  refine ⟨r, hr, fun T L hL => timeMap_realExpSegment hL ?_⟩
  rw [pointDelay_realExpSegment]
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  linear_combination -hroot

end Scalar

end MathlibExt.Analysis.ODE.DelayInstability
