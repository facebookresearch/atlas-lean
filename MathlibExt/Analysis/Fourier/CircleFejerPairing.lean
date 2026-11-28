/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.Fourier.CircleFejerCoefficients
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Fejér convergence against L¹ test functions

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and N∈ℕ, let
F_N(f)=circleFejerPolynomial f N be the continuous Fejér polynomial (N+1)⁻¹∑_{0≤i,j≤N}
f̂(i-j)e_(i-j). For f∈L∞(𝕋,μ) and h∈L¹(𝕋,μ), put P(f,h)=∫ x, f(x)h(x) ∂μ, the bilinear L∞–L¹
pairing. The L∞ classes f_N represented by F_N(f) satisfy ‖f_N‖L∞≤‖f‖L∞ and P(f_N,h)→P(f,h)
for every h∈L¹. The pairings have operator norms uniformly bounded by ‖f‖L∞.
-/

@[expose] public section
noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal InnerProductSpace
namespace MathlibExt.Analysis.Fourier

/-- **Hölder bound for the circle L∞–L¹ pairing.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and
h∈L¹(𝕋,μ), put P(f,h)=∫ x, f(x)h(x) ∂μ, the bilinear L∞–L¹ pairing. For f∈L∞ and h∈L¹,
|P(f,h)|≤‖f‖L∞‖h‖L¹.
-/
theorem circleLpPairing_norm_apply_le
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (h : Lp ℂ 1
      AddCircle.haarAddCircle) :
    ‖((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f h‖ ≤ ‖f‖ * ‖h‖ := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  have hI : ‖((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f h‖ ≤
    ‖B.holder 1 f h‖ := by
    change ‖L1.integralCLM' ℂ (B.holder 1 f h)‖ ≤ ‖B.holder 1 f h‖
    rw [← L1.integral_eq']
    exact L1.norm_integral_le _
  have hB := B.norm_holder_apply_apply_le (r := 1) f h
  have hm : ‖B‖ * ‖f‖ * ‖h‖ ≤ ‖f‖ * ‖h‖ := by
    have he := mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℂ ℂ)
      (mul_nonneg (norm_nonneg f) (norm_nonneg h))
    simpa only [one_mul, mul_assoc] using he
  exact hI.trans (hB.trans hm)

/-- **Operator norm of an L∞ pairing functional.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and
h∈L¹(𝕋,μ), put P(f,h)=∫ x, f(x)h(x) ∂μ, the bilinear L∞–L¹ pairing. For f∈L∞, the bounded
complex linear functional h↦P(f,h) on L¹(𝕋,μ) has norm at most ‖f‖L∞.
-/
theorem circleLpPairing_norm_le (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) :
    ‖((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f‖ ≤ ‖f‖ :=
  (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f).opNorm_le_bound
    (norm_nonneg f)
      (circleLpPairing_norm_apply_le f)

/-- **Fejér polynomial as an L∞ class.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and N∈ℕ, let
F_N(f)=circleFejerPolynomial f N be the continuous Fejér polynomial (N+1)⁻¹∑_{0≤i,j≤N}
f̂(i-j)e_(i-j). The class circleFejerLp f N∈L∞(𝕋,μ) is represented by the continuous
polynomial F_N(f).
-/
def circleFejerLp (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (N : ℕ) : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  (circleFejerPolynomial f N).toLp ∞ AddCircle.haarAddCircle ℂ


/-- **Contractive L∞ bound for Fejér classes.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and N∈ℕ, let
F_N(f)=circleFejerPolynomial f N be the continuous Fejér polynomial (N+1)⁻¹∑_{0≤i,j≤N}
f̂(i-j)e_(i-j). The L∞ class f_N=circleFejerLp f N satisfies ‖f_N‖L∞≤‖f‖L∞ for every N∈ℕ.
-/
theorem circleFejerLp_norm_le
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (N : ℕ) :
    ‖circleFejerLp f N‖ ≤ ‖f‖ := by
  have hC : ‖ContinuousMap.toLp (E := ℂ) ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)
    ℂ‖ ≤ 1 := by
    simpa only [ENNReal.toReal_top, inv_zero, Real.rpow_zero] using
      ContinuousMap.toLp_norm_le (E := ℂ)
        (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle)) (p := ∞) (𝕜 := ℂ)
  have hL := (ContinuousMap.toLp (E := ℂ) ∞
    (AddCircle.haarAddCircle : Measure UnitAddCircle) ℂ).le_opNorm (circleFejerPolynomial f N)
  exact hL.trans ((mul_le_mul_of_nonneg_right hC (norm_nonneg _)).trans
    (by rw [one_mul]; exact circleFejerPolynomial_norm_le f N))

/-- **Circle pairing with a Fourier monomial.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and
h∈L¹(𝕋,μ), put P(f,h)=∫ x, f(x)h(x) ∂μ, the bilinear L∞–L¹ pairing. For f∈L∞ and n∈ℤ,
P(f,e_n)=f̂(-n), where e_n is regarded as its L¹ class fourierLp 1 n. The pairing uses the
product f(x)e_n(x), without complex conjugation.
-/
theorem circleLpPairing_fourier
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (n : ℤ) :
    ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f (fourierLp 1 n) =
      fourierCoeff (f :
        UnitAddCircle → ℂ) (-n) := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  change (∫ x, f x * fourierLp 1 n x ∂AddCircle.haarAddCircle) =
    ∫ x, fourier (-(-n)) x • f x ∂AddCircle.haarAddCircle
  apply integral_congr_ae
  filter_upwards [coeFn_fourierLp 1 n] with x hx
  rw [hx, neg_neg, smul_eq_mul, mul_comm]

/-- **Fejér pairing convergence on Fourier monomials.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and N∈ℕ, let
F_N(f)=circleFejerPolynomial f N be the continuous Fejér polynomial (N+1)⁻¹∑_{0≤i,j≤N}
f̂(i-j)e_(i-j). For f∈L∞(𝕋,μ) and h∈L¹(𝕋,μ), put P(f,h)=∫ x, f(x)h(x) ∂μ, the bilinear L∞–L¹
pairing. For fixed n∈ℤ and f_N=circleFejerLp f N, P(f_N,e_n) tends to P(f,e_n)=f̂(-n) as N→∞.
-/
theorem circleFejerLp_pairing_fourier_tendsto
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (n : ℤ) :
    Tendsto (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞
      1) (circleFejerLp f N)
        (fourierLp 1 n)) atTop
      (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f (fourierLp
        1 n))) := by
  have he : ∀ N : ℕ,
      ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) (circleFejerLp f
        N) (fourierLp 1 n) =
        fourierCoeff (fun x : UnitAddCircle => circleFejerPolynomial f N x) (-n) := by
    intro N
    rw [circleLpPairing_fourier]
    exact congrFun (fourierCoeff_congr_ae
      (ContinuousMap.coeFn_toLp AddCircle.haarAddCircle (circleFejerPolynomial f N))) (-n)
  simp_rw [he, circleLpPairing_fourier]
  exact circleFejerPolynomial_fourierCoeff_tendsto f (-n)

/-- **Equicontinuity of Fejér pairing functionals.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and N∈ℕ, let
F_N(f)=circleFejerPolynomial f N be the continuous Fejér polynomial (N+1)⁻¹∑_{0≤i,j≤N}
f̂(i-j)e_(i-j). For f∈L∞(𝕋,μ) and h∈L¹(𝕋,μ), put P(f,h)=∫ x, f(x)h(x) ∂μ, the bilinear L∞–L¹
pairing. For fixed f∈L∞, the family of functions h↦P(circleFejerLp f N,h), N∈ℕ, is
equicontinuous on L¹(𝕋,μ), with uniform operator norm bound ‖f‖L∞.
-/
theorem circleFejerPairing_equicontinuous
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) :
    Equicontinuous (fun N : ℕ => (((ContinuousLinearMap.mul ℂ ℂ).lpPairing
      AddCircle.haarAddCircle ∞ 1)
        (circleFejerLp f N) : Lp ℂ 1 AddCircle.haarAddCircle → ℂ)) := by
  let L : ℕ → Lp ℂ 1 AddCircle.haarAddCircle →L[ℂ] ℂ := fun N =>
    ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
      (circleFejerLp f N)
  change Equicontinuous ((↑) ∘ L)
  apply ((NormedSpace.equicontinuous_tfae L).out 6 2).mp
  exact ⟨‖f‖, fun N =>
    (circleLpPairing_norm_le _).trans (circleFejerLp_norm_le f N)⟩

/-- **Fejér pairing convergence for every L¹ coefficient.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and N∈ℕ, let
F_N(f)=circleFejerPolynomial f N be the continuous Fejér polynomial (N+1)⁻¹∑_{0≤i,j≤N}
f̂(i-j)e_(i-j). For f∈L∞(𝕋,μ) and h∈L¹(𝕋,μ), put P(f,h)=∫ x, f(x)h(x) ∂μ, the bilinear L∞–L¹
pairing. For every h∈L¹(𝕋,μ), P(circleFejerLp f N,h) tends to P(f,h) as N→∞.
-/
theorem circleFejerLp_pairing_tendsto
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (h : Lp ℂ 1
      AddCircle.haarAddCircle) :
    Tendsto (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞
      1) (circleFejerLp f N)
        h) atTop (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f
          h)) := by
  let M : Submodule ℂ (Lp ℂ 1 (AddCircle.haarAddCircle : Measure UnitAddCircle)) :=
    { carrier := {h | Tendsto (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
      AddCircle.haarAddCircle ∞ 1)
        (circleFejerLp f N) h) atTop
        (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f h))}
      zero_mem' := by
        change Tendsto
          (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
            (circleFejerLp f N) 0) atTop
          (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f 0))
        simpa only [map_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (0 : ℂ)))
      add_mem' := by
        intro h₁ h₂ hh₁ hh₂
        change Tendsto
          (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
            (circleFejerLp f N) h₁) atTop
          (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f h₁)) at hh₁
        change Tendsto
          (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
            (circleFejerLp f N) h₂) atTop
          (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f h₂)) at hh₂
        change Tendsto
          (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
            (circleFejerLp f N) (h₁ + h₂)) atTop
          (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f (h₁ + h₂)))
        simpa only [map_add] using hh₁.add hh₂
      smul_mem' := by
        intro c h hh
        change Tendsto
          (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
            (circleFejerLp f N) h) atTop
          (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f h)) at hh
        change Tendsto
          (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
            (circleFejerLp f N) (c • h)) atTop
          (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f (c • h)))
        simpa only [map_smul] using hh.const_smul c }
  have hclosed : IsClosed (M : Set (Lp ℂ 1 (AddCircle.haarAddCircle : Measure UnitAddCircle))) := by
    change IsClosed {h : Lp ℂ 1 (AddCircle.haarAddCircle : Measure UnitAddCircle) |
      Tendsto (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
        (circleFejerLp f N) h) atTop
        (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f h))}
    exact Equicontinuous.isClosed_setOfPred_tendsto
      (l := (atTop : Filter ℕ))
      (F := fun N : ℕ =>
        (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) (circleFejerLp f N) :
          Lp ℂ 1 (AddCircle.haarAddCircle : Measure UnitAddCircle) → ℂ))
      (f := (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f :
        Lp ℂ 1 (AddCircle.haarAddCircle : Measure UnitAddCircle) → ℂ))
      (circleFejerPairing_equicontinuous f)
      (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f).continuous
  have hspan : Submodule.span ℂ (Set.range (fourierLp 1 (T := (1 : ℝ)))) ≤ M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change Tendsto
      (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
        (circleFejerLp f N) (fourierLp 1 n)) atTop
      (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f (fourierLp 1 n)))
    exact circleFejerLp_pairing_fourier_tendsto f n
  have hclosure :
      (Submodule.span ℂ (Set.range (fourierLp 1 (T := (1 : ℝ))))).topologicalClosure ≤ M :=
    Submodule.topologicalClosure_minimal _ hspan hclosed
  have hdense := span_fourierLp_closure_eq_top (T := (1 : ℝ)) (p := 1) (by simp : (1 : ℝ≥0∞) ≠ ∞)
  rw [hdense] at hclosure
  change h ∈ M
  exact hclosure Submodule.mem_top

end MathlibExt.Analysis.Fourier
