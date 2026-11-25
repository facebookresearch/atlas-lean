/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import MathlibExt.Analysis.ODE.Duhamel

/-!
# Controllability of linear control systems

For the time-invariant linear control system `ẋ = A x + B u` on finite-dimensional real inner
product spaces (state space `E`, control space `U`), this file defines controllability on a time
interval `[0, T]`, the controllability Gramian and the Kalman subspace, and proves the two
classical criteria that Coron attributes to Kalman, Ho and Narendra (1963):

* `isControllableOn_iff_bijective_gramian`: controllable on `[0, T]` iff the controllability
  Gramian is invertible (Coron, *Control and Nonlinearity*, Theorem 1.11, time-invariant case);
* `isControllableOn_iff_kalman`: controllable on `[0, T]` iff the Kalman rank condition holds
  (Coron, Theorem 1.16; Sontag, *Mathematical Control Theory*, 2nd ed., Theorem 3).

Controls are continuous functions of time. Coron's Definition 1.2 uses `L^∞` controls. The two
notions agree for these time-invariant systems: an `L^∞`-controllable system has an invertible
Gramian by Coron's Theorem 1.11, and then the Gramian criterion proved here gives continuous
controls; conversely continuous controls on `[0, T]` are `L^∞` (compare Coron's Remark 1.3, which
treats `L²` and `L¹`).
-/

open MeasureTheory Set

@[expose] public section

namespace MathlibExt.Analysis.Control

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- **Controllability of a linear control system.** The system `ẋ = A x + B u` is
controllable on `[0, T]` if every state `x₀` can be steered to every state `x₁`: there is a
continuous control `u` and a solution `x` of `ẋ(t) = A x(t) + B u(t)` with `x 0 = x₀` and
`x T = x₁` (Coron, *Control and Nonlinearity*, AMS 2007, Definition 1.2, with continuous instead
of `L^∞` controls; the notions agree by Coron's Theorem 1.11 together with the Gramian criterion
`isControllableOn_iff_bijective_gramian`, compare his Remark 1.3). -/
def IsControllableOn (A : E →L[ℝ] E) (B : U →L[ℝ] E) (T : ℝ) : Prop :=
  ∀ x₀ x₁ : E, ∃ u : ℝ → U, Continuous u ∧ ∃ x : ℝ → E, x 0 = x₀ ∧
    (∀ t, HasDerivAt x (A (x t) + B (u t)) t) ∧ x T = x₁

/-- **Controllability Gramian.** For `ẋ = A x + B u` on `[0, T]`, the operator
`W_T = ∫₀ᵀ e^{sA} B B* e^{sA*} ds`. This is Coron's Definition 1.10,
`C = ∫_{T₀}^{T₁} R(T₁, τ) B B^tr R(T₁, τ)^tr dτ` with resolvent `R(T₁, τ) = e^{(T₁ - τ) A}`,
after the change of variables `s = T₁ - τ` and with `[T₀, T₁] = [0, T]`. -/
noncomputable def gramian (A : E →L[ℝ] E) (B : U →L[ℝ] E) (T : ℝ) : E →L[ℝ] E :=
  ∫ s in (0 : ℝ)..T, NormedSpace.exp (s • A) ∘L B ∘L ContinuousLinearMap.adjoint B ∘L
    ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))

/-- **Kalman subspace.** The span of the vectors `A^i B u` for `u ∈ U` and
`0 ≤ i < dim E`; the Kalman rank condition says that it is the whole state space (Coron,
Theorem 1.16, condition (1.29)). -/
def kalmanSubspace (A : E →L[ℝ] E) (B : U →L[ℝ] E) : Submodule ℝ E :=
  Submodule.span ℝ {x | ∃ i < Module.finrank ℝ E, ∃ u : U, x = (A ^ i) (B u)}

private theorem continuous_exp_smul (A : E →L[ℝ] E) :
    Continuous fun s : ℝ => NormedSpace.exp (s • A) :=
  (differentiable_exp_smul_const ℝ A).continuous

private theorem continuous_gramian_integrand (A : E →L[ℝ] E) (B : U →L[ℝ] E) :
    Continuous fun s : ℝ => NormedSpace.exp (s • A) ∘L B ∘L ContinuousLinearMap.adjoint B ∘L
      ContinuousLinearMap.adjoint (NormedSpace.exp (s • A)) := by
  have he := continuous_exp_smul A
  have hadj : Continuous fun s : ℝ => ContinuousLinearMap.adjoint (NormedSpace.exp (s • A)) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := E)).continuous.comp he
  exact he.clm_comp (continuous_const.clm_comp (continuous_const.clm_comp hadj))

omit [FiniteDimensional ℝ U] in
/-- The endpoint of every solution with continuous control is given by the variation of
constants formula. -/
private theorem endpoint_eq (A : E →L[ℝ] E) (B : U →L[ℝ] E) (T : ℝ) (u : ℝ → U)
    (hu : Continuous u) (x : ℝ → E) (hx : ∀ t, HasDerivAt x (A (x t) + B (u t)) t) :
    x T = NormedSpace.exp (T • A) (x 0) +
      ∫ s in (0 : ℝ)..T, NormedSpace.exp ((T - s) • A) (B (u s)) := by
  obtain ⟨y, hy0, hy, -, huniq⟩ :=
    MathlibExt.Analysis.ODE.DuhamelWanted.duhamel_variation_of_constants
      A (fun t => B (u t)) 0 (x 0) (B.continuous.comp hu)
  rw [huniq x rfl hx, hy T, hy0]
  simp

omit [FiniteDimensional ℝ U] in
/-- Every continuous control has a solution from every initial state. -/
private theorem exists_solution (A : E →L[ℝ] E) (B : U →L[ℝ] E) (u : ℝ → U)
    (hu : Continuous u) (x₀ : E) :
    ∃ x : ℝ → E, x 0 = x₀ ∧ ∀ t, HasDerivAt x (A (x t) + B (u t)) t := by
  obtain ⟨y, hy0, -, hy, -⟩ := MathlibExt.Analysis.ODE.DuhamelWanted.duhamel_variation_of_constants
    A (fun t => B (u t)) 0 x₀ (B.continuous.comp hu)
  exact ⟨y, hy0, hy⟩

/-- **Quadratic form of the Gramian.** `⟪η, W_T η⟫ = ∫₀ᵀ ‖B* e^{sA*} η‖² ds`
(Coron, Remark 1.12). -/
theorem inner_gramian_apply (A : E →L[ℝ] E) (B : U →L[ℝ] E) (T : ℝ) (η : E) :
    ⟪η, gramian A B T η⟫ = ∫ s in (0 : ℝ)..T, ‖ContinuousLinearMap.adjoint B
      (ContinuousLinearMap.adjoint (NormedSpace.exp (s • A)) η)‖ ^ 2 := by
  have hint := (continuous_gramian_integrand A B).intervalIntegrable (μ := volume) 0 T
  rw [gramian, ContinuousLinearMap.intervalIntegral_apply hint]
  have hint' : IntervalIntegrable (fun s : ℝ => (NormedSpace.exp (s • A) ∘L B ∘L
      ContinuousLinearMap.adjoint B ∘L ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))) η)
      volume 0 T :=
    ((continuous_gramian_integrand A B).clm_apply continuous_const).intervalIntegrable 0 T
  have := (innerSL ℝ η).intervalIntegral_comp_comm hint'
  rw [innerSL_apply_apply] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [innerSL_apply_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.adjoint_inner_left,
    real_inner_self_eq_norm_sq]

/-- A continuous nonnegative function with zero integral over `[0, T]` vanishes on `[0, T]`. -/
private theorem eqOn_zero_of_integral_eq_zero {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : Continuous f) (hpos : ∀ s, 0 ≤ f s) (hint : ∫ s in (0 : ℝ)..T, f s = 0) :
    ∀ s ∈ Icc 0 T, f s = 0 := by
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hT.le
    (Filter.Eventually.of_forall hpos) (hf.intervalIntegrable 0 T)).1 hint
  have hIoo : ∀ s ∈ Ioo 0 T, f s = 0 := by
    intro s hs
    by_contra hne
    set V := {t | f t ≠ 0} ∩ Ioo 0 T with hV
    have hVo : IsOpen V := (isOpen_ne_fun hf continuous_const).inter isOpen_Ioo
    have hVpos : 0 < volume V := hVo.measure_pos volume ⟨s, hne, hs⟩
    have hmeas : MeasurableSet {t | f t ≠ 0} := (isOpen_ne_fun hf continuous_const).measurableSet
    have hzero : volume ({t | f t ≠ 0} ∩ Ioc 0 T) = 0 := by
      rw [← Measure.restrict_apply hmeas]
      exact hae
    have hle : volume V ≤ volume ({t | f t ≠ 0} ∩ Ioc 0 T) :=
      measure_mono (inter_subset_inter_right _ Ioo_subset_Ioc_self)
    exact absurd (hzero ▸ hle) (not_le.2 hVpos)
  intro s hs
  have hcl : closure (Ioo (0 : ℝ) T) = Icc 0 T := closure_Ioo hT.ne
  have hclosed : IsClosed {t | f t = 0} := isClosed_eq hf continuous_const
  have hsub : Ioo (0 : ℝ) T ⊆ {t | f t = 0} := hIoo
  exact (hclosed.closure_subset_iff.2 hsub) (hcl ▸ hs)

/-- If `W_T η = 0` then `η` is orthogonal to `e^{sA} B v` for all `s ∈ [0, T]` and all `v`. -/
private theorem inner_exp_eq_zero_of_gramian {A : E →L[ℝ] E} {B : U →L[ℝ] E} {T : ℝ}
    (hT : 0 < T) {η : E} (hη : gramian A B T η = 0) :
    ∀ s ∈ Icc 0 T, ∀ v : U, ⟪η, NormedSpace.exp (s • A) (B v)⟫ = 0 := by
  have hq := inner_gramian_apply A B T η
  rw [hη, inner_zero_right] at hq
  have hc : Continuous fun s : ℝ => ContinuousLinearMap.adjoint B
      (ContinuousLinearMap.adjoint (NormedSpace.exp (s • A)) η) := by
    have hadj : Continuous fun s : ℝ => ContinuousLinearMap.adjoint (NormedSpace.exp (s • A)) :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := E)).continuous.comp
        (continuous_exp_smul A)
    exact continuous_const.clm_apply (hadj.clm_apply continuous_const)
  have h0 := eqOn_zero_of_integral_eq_zero hT (hc.norm.pow 2) (fun s => sq_nonneg _) hq.symm
  intro s hs v
  have hs0 : ContinuousLinearMap.adjoint B
      (ContinuousLinearMap.adjoint (NormedSpace.exp (s • A)) η) = 0 := by
    have := h0 s hs
    simpa using this
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.adjoint_inner_left, hs0,
    inner_zero_left]

omit [FiniteDimensional ℝ U] in
/-- If `η` is orthogonal to `e^{sA} B v` for all `s ∈ [0, T]`, then it is orthogonal to the
contribution of every continuous control to the endpoint. -/
private theorem inner_integral_eq_zero {A : E →L[ℝ] E} {B : U →L[ℝ] E} {T : ℝ} (hT : 0 < T)
    {η : E} (h : ∀ s ∈ Icc 0 T, ∀ v : U, ⟪η, NormedSpace.exp (s • A) (B v)⟫ = 0)
    (u : ℝ → U) (hu : Continuous u) :
    ⟪η, ∫ s in (0 : ℝ)..T, NormedSpace.exp ((T - s) • A) (B (u s))⟫ = 0 := by
  have hc : Continuous fun s : ℝ => NormedSpace.exp ((T - s) • A) (B (u s)) :=
    ((continuous_exp_smul A).comp (continuous_const.sub continuous_id)).clm_apply
      (B.continuous.comp hu)
  have := (innerSL ℝ η).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 T)
  rw [innerSL_apply_apply] at this
  rw [← this]
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
  · simp
  intro s hs
  rw [uIcc_of_le hT.le] at hs
  simp only [innerSL_apply_apply]
  exact h (T - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩ (u s)

/-- **Gramian criterion for controllability** (Coron, *Control and Nonlinearity*, AMS 2007,
Theorem 1.11, here for time-invariant systems; Coron attributes it to Kalman, Ho and Narendra
1963, Theorem 5). For `T > 0`, the
system `ẋ = A x + B u` is controllable on `[0, T]` if and only if its controllability Gramian
`W_T` is invertible. -/
theorem isControllableOn_iff_bijective_gramian (A : E →L[ℝ] E) (B : U →L[ℝ] E) {T : ℝ}
    (hT : 0 < T) : IsControllableOn A B T ↔ Function.Bijective (gramian A B T) := by
  have hinj_iff : Function.Bijective (gramian A B T) ↔ Function.Injective (gramian A B T) := by
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, (LinearMap.injective_iff_surjective (f := (gramian A B T : E →ₗ[ℝ] E))).1 h⟩
  rw [hinj_iff]
  constructor
  · intro hc
    rw [injective_iff_map_eq_zero]
    intro η hη
    obtain ⟨u, hu, x, hx0, hx, hxT⟩ := hc 0 η
    have hend := endpoint_eq A B T u hu x hx
    rw [hxT, hx0, map_zero, zero_add] at hend
    have h0 := inner_integral_eq_zero hT (inner_exp_eq_zero_of_gramian hT hη) u hu
    rw [← hend] at h0
    exact inner_self_eq_zero.1 h0
  · intro hinj x₀ x₁
    have hsurj : Function.Surjective (gramian A B T) :=
      (LinearMap.injective_iff_surjective (f := (gramian A B T : E →ₗ[ℝ] E))).1 hinj
    obtain ⟨ξ, hξ⟩ := hsurj (x₁ - NormedSpace.exp (T • A) x₀)
    set u : ℝ → U := fun s => ContinuousLinearMap.adjoint B
      (ContinuousLinearMap.adjoint (NormedSpace.exp ((T - s) • A)) ξ) with hu_def
    have hu : Continuous u := by
      have hadj : Continuous fun s : ℝ =>
          ContinuousLinearMap.adjoint (NormedSpace.exp ((T - s) • A)) :=
        (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := E)).continuous.comp
          ((continuous_exp_smul A).comp (continuous_const.sub continuous_id))
      exact continuous_const.clm_apply (hadj.clm_apply continuous_const)
    obtain ⟨x, hx0, hx⟩ := exists_solution A B u hu x₀
    refine ⟨u, hu, x, hx0, hx, ?_⟩
    rw [endpoint_eq A B T u hu x hx, hx0]
    have hW : (∫ s in (0 : ℝ)..T, NormedSpace.exp ((T - s) • A) (B (u s))) =
        gramian A B T ξ := by
      rw [gramian, ContinuousLinearMap.intervalIntegral_apply
        ((continuous_gramian_integrand A B).intervalIntegrable 0 T)]
      have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := T)
        (fun s : ℝ => (NormedSpace.exp (s • A) ∘L B ∘L ContinuousLinearMap.adjoint B ∘L
          ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))) ξ) T
      simp only [sub_self, sub_zero] at this
      rw [← this]
      rfl
    rw [hW, hξ]
    abel

omit [FiniteDimensional ℝ U] in
/-- `A^k x` lies in the span of `x, A x, …, A^{n-1} x`, `n = dim E` (Cayley–Hamilton). -/
private theorem pow_apply_mem_kalmanSubspace (A : E →L[ℝ] E) (B : U →L[ℝ] E) (k : ℕ) (v : U) :
    (A ^ k) (B v) ∈ kalmanSubspace A B := by
  set n := Module.finrank ℝ E
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have : Subsingleton E := Module.finrank_zero_iff.1 hn
    rw [Subsingleton.elim ((A ^ k) (B v)) 0]
    exact Submodule.zero_mem _
  set f : Module.End ℝ E := (A : E →ₗ[ℝ] E)
  have hpow : ((A ^ k : E →L[ℝ] E) : E →ₗ[ℝ] E) = f ^ k := ContinuousLinearMap.toLinearMap_pow A k
  have hdeg : (Polynomial.X ^ k %ₘ f.charpoly).natDegree < n := by
    have hmon := LinearMap.charpoly_monic f
    have hne : f.charpoly ≠ 1 := by
      intro h
      have := LinearMap.charpoly_natDegree f
      rw [h, Polynomial.natDegree_one] at this
      omega
    have := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ k) hmon hne
    rwa [LinearMap.charpoly_natDegree] at this
  have hk : (A ^ k) (B v) = ((f ^ k) (B v)) := by
    rw [← hpow]; rfl
  rw [hk, LinearMap.pow_eq_aeval_mod_charpoly, Polynomial.aeval_eq_sum_range' hdeg]
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_range.1 hi, v, ?_⟩)
  rw [← ContinuousLinearMap.toLinearMap_pow]; rfl

omit [FiniteDimensional ℝ U] in
/-- If `η ⊥ A^k B v` for all `k`, `v`, then `η ⊥ e^{sA} B v` for all `s`, `v`. -/
private theorem inner_exp_eq_zero_of_forall_pow {A : E →L[ℝ] E} {B : U →L[ℝ] E} {η : E}
    (h : ∀ k (v : U), ⟪η, (A ^ k) (B v)⟫ = 0) (s : ℝ) (v : U) :
    ⟪η, NormedSpace.exp (s • A) (B v)⟫ = 0 := by
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (s • A)
  have hmap := hs.mapL ((innerSL ℝ η).comp (ContinuousLinearMap.apply ℝ E (B v)))
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.apply_apply, innerSL_apply_apply] at hmap
  refine hmap.unique ?_
  convert hasSum_zero with k
  rw [smul_pow, smul_apply, smul_apply, inner_smul_right,
    inner_smul_right, h k v, mul_zero, mul_zero]

omit [FiniteDimensional ℝ U] in
/-- **Kalman rank condition, dual form.** `Span {A^i B u : u ∈ U, 0 ≤ i < dim E} = E` if and
only if no nonzero vector is orthogonal to every `A^k B v`, `k ∈ ℕ`, `v ∈ U` (the powers `k ≥ dim E`
add nothing, by the Cayley–Hamilton theorem). -/
theorem kalmanSubspace_eq_top_iff (A : E →L[ℝ] E) (B : U →L[ℝ] E) :
    kalmanSubspace A B = ⊤ ↔ ∀ η : E, (∀ (k : ℕ) (v : U), ⟪η, (A ^ k) (B v)⟫ = 0) → η = 0 := by
  constructor
  · intro hK η hη
    have hspan : ∀ x ∈ kalmanSubspace A B, ⟪η, x⟫ = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, -, v, rfl⟩ := hy
        exact hη i v
      | zero => exact inner_zero_right η
      | add y z _ _ hy hz => rw [inner_add_right, hy, hz, add_zero]
      | smul a y _ hy => rw [inner_smul_right, hy, mul_zero]
    exact inner_self_eq_zero.1 (hspan η (hK ▸ Submodule.mem_top))
  · intro h
    by_contra hne
    have hperp : (kalmanSubspace A B)ᗮ ≠ ⊥ := by
      rwa [Ne, Submodule.orthogonal_eq_bot_iff]
    obtain ⟨η, hηmem, hη0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
    exact hη0 (h η fun k v =>
      Submodule.inner_left_of_mem_orthogonal (pow_apply_mem_kalmanSubspace A B k v) hηmem)

omit [FiniteDimensional ℝ U] in
/-- If `η ⊥ e^{sA} B v` for all `s ∈ [0, T]` and `v`, then `η ⊥ e^{sA} A^k B v` as well, by
differentiating in `s`. -/
private theorem inner_exp_pow_eq_zero {A : E →L[ℝ] E} {B : U →L[ℝ] E} {T : ℝ} (hT : 0 < T)
    {η : E} (h : ∀ s ∈ Icc 0 T, ∀ v : U, ⟪η, NormedSpace.exp (s • A) (B v)⟫ = 0) (k : ℕ) :
    ∀ s ∈ Icc 0 T, ∀ v : U, ⟪η, NormedSpace.exp (s • A) ((A ^ k) (B v))⟫ = 0 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    intro s hs v
    set w := (A ^ k) (B v) with hw
    have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ⟪η, NormedSpace.exp (t • A) w⟫)
        ⟪η, NormedSpace.exp (t • A) (A w)⟫ t := by
      intro t
      have h1 := HasDerivAt.clm_apply (hasDerivAt_exp_smul_const A t) (hasDerivAt_const t w)
      have h2 := ((innerSL ℝ η).hasFDerivAt).comp_hasDerivAt t h1
      convert h2 using 1
      · rfl
      · simp [innerSL_apply_apply, mul_apply_eq_comp]
    have hc : Continuous fun t : ℝ => ⟪η, NormedSpace.exp (t • A) (A w)⟫ :=
      continuous_const.inner ((continuous_exp_smul A).clm_apply continuous_const)
    have hIoo : ∀ t ∈ Ioo 0 T, ⟪η, NormedSpace.exp (t • A) (A w)⟫ = 0 := by
      intro t ht
      have hev : (fun t : ℝ => ⟪η, NormedSpace.exp (t • A) w⟫) =ᶠ[nhds t] fun _ => 0 := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
        exact ih r (Ioo_subset_Icc_self hr) v
      exact (hderiv t).unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev)
    have hcl : closure (Ioo (0 : ℝ) T) = Icc 0 T := closure_Ioo hT.ne
    have hclosed : IsClosed {t : ℝ | ⟪η, NormedSpace.exp (t • A) (A w)⟫ = 0} :=
      isClosed_eq hc continuous_const
    have hmem := (hclosed.closure_subset_iff.2 hIoo) (hcl ▸ hs)
    simpa [hw, pow_succ', mul_apply_eq_comp] using hmem

/-- **Kalman rank condition** (Coron, *Control and Nonlinearity*, AMS 2007, Theorem 1.16, which
Coron attributes to Kalman, Ho and Narendra 1963, Theorem 10; Sontag, *Mathematical Control
Theory*, 2nd ed., Theorem 3). For
`T > 0`, the system `ẋ = A x + B u` is controllable on `[0, T]` if and only if
`Span {A^i B u : u ∈ U, 0 ≤ i < dim E}` is the whole state space. In particular controllability
does not depend on `T > 0`. -/
theorem isControllableOn_iff_kalman (A : E →L[ℝ] E) (B : U →L[ℝ] E) {T : ℝ} (hT : 0 < T) :
    IsControllableOn A B T ↔ kalmanSubspace A B = ⊤ := by
  rw [isControllableOn_iff_bijective_gramian A B hT]
  constructor
  · intro hbij
    by_contra hne
    have hperp : (kalmanSubspace A B)ᗮ ≠ ⊥ := by
      rwa [Ne, Submodule.orthogonal_eq_bot_iff]
    obtain ⟨η, hηmem, hη0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
    have hpow : ∀ k (v : U), ⟪η, (A ^ k) (B v)⟫ = 0 := fun k v =>
      Submodule.inner_left_of_mem_orthogonal (pow_apply_mem_kalmanSubspace A B k v) hηmem
    have hB : ∀ s : ℝ, ContinuousLinearMap.adjoint B
        (ContinuousLinearMap.adjoint (NormedSpace.exp (s • A)) η) = 0 := by
      intro s
      apply ext_inner_right ℝ
      intro v
      rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
        inner_zero_left]
      exact inner_exp_eq_zero_of_forall_pow hpow s v
    apply hη0
    apply hbij.1
    rw [map_zero, gramian, ContinuousLinearMap.intervalIntegral_apply
      ((continuous_gramian_integrand A B).intervalIntegrable 0 T)]
    simp [hB]
  · intro hK
    refine ⟨?_, (LinearMap.injective_iff_surjective
      (f := (gramian A B T : E →ₗ[ℝ] E))).1 ?_⟩ <;>
    · rw [injective_iff_map_eq_zero]
      intro η hη
      have h0 := inner_exp_pow_eq_zero hT (inner_exp_eq_zero_of_gramian hT hη)
      have hspan : ∀ x ∈ kalmanSubspace A B, ⟪η, x⟫ = 0 := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, -, v, rfl⟩ := hy
          simpa using h0 i 0 ⟨le_rfl, hT.le⟩ v
        | zero => exact inner_zero_right η
        | add y z _ _ hy hz => rw [inner_add_right, hy, hz, add_zero]
        | smul a y _ hy => rw [inner_smul_right, hy, mul_zero]
      exact inner_self_eq_zero.1 (hspan η (hK ▸ Submodule.mem_top))

end MathlibExt.Analysis.Control
