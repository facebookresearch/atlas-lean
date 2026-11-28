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

public import MathlibExt.Analysis.Fourier.CircleFejerPolynomial
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Fourier coefficients of Fejér polynomials

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and N∈ℕ, let
F_N(f)=circleFejerPolynomial f N be the continuous Fejér polynomial (N+1)⁻¹∑_{0≤i,j≤N}
f̂(i-j)e_(i-j). Put w_N(k)=circleFejerWeight N k=(N+1-|k|)_+/(N+1), viewed as a complex
scalar, where (·)_+ is truncation at zero. Every coefficient satisfies F_N(f)̂(k)=w_N(k)f̂(k),
including zero for |k|>N. For each fixed k, w_N(k)→1 and F_N(f)̂(k)→f̂(k) as N→∞.
-/

@[expose] public section
noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal InnerProductSpace
namespace MathlibExt.Analysis.Fourier

/-- **Finite difference-frequency sum.**

For N∈ℕ, k∈ℤ and c∈ℂ, circleDifferenceSum N k c=∑_{0≤i,j≤N} (if k=i-j then c else 0). It
counts each occurrence of the difference k in the square index range.
-/
def circleDifferenceSum (N : ℕ) (k : ℤ) (c : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), if k = (i : ℤ) - j then c else 0

/-- **A row of the nonnegative difference-frequency sum.**

Let N,k,i∈ℕ with i<N+1 and c∈ℂ. Then ∑_{j=0}^N (if k=i-j then c else 0) is c when k≤i and zero
otherwise, with the difference compared in ℤ.
-/
theorem circleDifferenceSum_row (N k i : ℕ) (hi : i < N + 1) (c : ℂ) :
    (∑ j ∈ Finset.range (N + 1), if (k : ℤ) = (i : ℤ) - j then c else 0) =
      if k ≤ i then c else 0 := by
  by_cases hk : k ≤ i
  · rw [ite_eq_left hk]
    have hm : i - k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single (i - k)]
    · have he : (k : ℤ) = (i : ℤ) - ((i - k : ℕ) : ℤ) := by omega
      rw [ite_eq_left he]
    · intro j hj hne
      exact ite_eq_right (by omega)
    · intro hnot
      exact False.elim (hnot hm)
  · rw [ite_eq_right hk]
    exact Finset.sum_eq_zero (fun j hj => ite_eq_right (by omega))

/-- **Multiplicity of a nonnegative difference frequency.**

For N,k∈ℕ and c∈ℂ, the sum D_N(k,c)=∑_{0≤i,j≤N}(if k=i-j then c else 0) equals (N+1-k)•c,
where natural subtraction gives zero for k>N.
-/
theorem circleDifferenceSum_nat (N k : ℕ) (c : ℂ) :
    circleDifferenceSum N (k : ℤ) c = (N + 1 - k : ℕ) • c := by
  unfold circleDifferenceSum
  have hrow : (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
      if (k : ℤ) = (i : ℤ) - j then c else 0) =
      ∑ i ∈ Finset.range (N + 1), if k ≤ i then c else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact circleDifferenceSum_row N k i (Finset.mem_range.mp hi) c
  rw [hrow]
  by_cases hk : k ≤ N
  · have hn : N + 1 = k + (N + 1 - k) := by omega
    rw [hn, Finset.sum_range_add]
    have hleft : (∑ i ∈ Finset.range k, if k ≤ i then c else 0) = 0 :=
      Finset.sum_eq_zero (fun i hi => ite_eq_right (by have h := Finset.mem_range.mp hi; omega))
    have hright : (∑ i ∈ Finset.range (N + 1 - k), if k ≤ k + i then c else 0) =
        (N + 1 - k : ℕ) • c := by
      simp only [Nat.le_add_right, ite_true, Finset.sum_const, Finset.card_range]
    rw [hleft, hright, zero_add, Nat.add_sub_cancel_left]
  · have hn : N + 1 - k = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hn, zero_nsmul]
    apply Finset.sum_eq_zero
    intro i hi
    exact ite_eq_right (by have hi' := Finset.mem_range.mp hi; omega)

/-- **Symmetry of difference-frequency counts.**

For N∈ℕ, k∈ℤ and c∈ℂ, circleDifferenceSum N (-k) c=circleDifferenceSum N k c, where the sum
counts pairs 0≤i,j≤N with difference i-j=k.
-/
theorem circleDifferenceSum_neg (N : ℕ) (k : ℤ) (c : ℂ) :
    circleDifferenceSum N (-k) c = circleDifferenceSum N k c := by
  unfold circleDifferenceSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have he : (-k = (j : ℤ) - i) ↔ (k = (i : ℤ) - j) := by omega
  exact if_congr he rfl rfl

/-- **Normalized Fejér Fourier weight.**

For N∈ℕ and k∈ℤ, circleFejerWeight N k=(N+1-|k|)_+/(N+1) as a complex scalar. It is 1 at k=0
and zero when |k|≥N+1.
-/
def circleFejerWeight (N : ℕ) (k : ℤ) : ℂ :=
  (N + 1 : ℂ)⁻¹ * (N + 1 - k.natAbs : ℕ)

/-- **Normalized difference counts equal Fejér weights.**

For N∈ℕ, k∈ℤ and c∈ℂ, (N+1)⁻¹ circleDifferenceSum N k c=circleFejerWeight N k*c, where the
difference sum counts pairs 0≤i,j≤N with i-j=k and the weight is (N+1-|k|)_+/(N+1).
-/
theorem circleDifferenceSum_eq (N : ℕ) (k : ℤ) (c : ℂ) :
    (N + 1 : ℂ)⁻¹ * circleDifferenceSum N k c = circleFejerWeight N k * c := by
  have he : circleDifferenceSum N k c = (N + 1 - k.natAbs : ℕ) • c := by
    by_cases hsign : 0 ≤ k
    · have hnat : ((k.natAbs : ℕ) : ℤ) = k := by omega
      rw [← hnat]
      exact circleDifferenceSum_nat N k.natAbs c
    · have hneg : k = -((k.natAbs : ℕ) : ℤ) := by omega
      rw [hneg, circleDifferenceSum_neg]
      simpa only [Int.natAbs_neg, Int.natAbs_natCast] using circleDifferenceSum_nat N k.natAbs c
  rw [he]
  simp only [circleFejerWeight, nsmul_eq_mul, mul_assoc]

/-- **Fourier coefficient from the finite Fejér difference sum.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and N∈ℕ, let
F_N(f)=circleFejerPolynomial f N be the continuous Fejér polynomial (N+1)⁻¹∑_{0≤i,j≤N}
f̂(i-j)e_(i-j). For k∈ℤ, F_N(f)̂(k)=(N+1)⁻¹ circleDifferenceSum N k (f̂(k)), where
circleDifferenceSum counts the pairs 0≤i,j≤N with i-j=k.
-/
theorem circleFejerPolynomial_fourierCoeff_sum
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (N : ℕ) (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => circleFejerPolynomial f N x) k =
      (N + 1 : ℂ)⁻¹ * circleDifferenceSum N k (fourierCoeff (f : UnitAddCircle → ℂ) k) := by
  have hterm : ∀ i j : ℕ,
      Integrable (fun x : UnitAddCircle =>
        fourierCoeff (f : UnitAddCircle → ℂ) ((i : ℤ) - (j : ℤ)) *
          fourier ((i : ℤ) - (j : ℤ)) x) AddCircle.haarAddCircle := by
    intro i j
    have hm := ContinuousMap.memLp (p := (1 : ℝ≥0∞))
      (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle)) ℂ
      (fourier ((i : ℤ) - (j : ℤ)))
    exact (memLp_one_iff_integrable.mp hm).const_mul _
  have hfun : (fun x : UnitAddCircle => circleFejerPolynomial f N x) =
      (N + 1 : ℂ)⁻¹ •
        (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
          (fun x : UnitAddCircle =>
            fourierCoeff (f : UnitAddCircle → ℂ) ((i : ℤ) - (j : ℤ)) *
              fourier ((i : ℤ) - (j : ℤ)) x)) := by
    funext x
    simp only [circleFejerPolynomial, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
      Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [hfun, fourierCoeff.const_smul]
  change (N + 1 : ℂ)⁻¹ * _ = _
  congr 1
  have hout := fourierCoeff.sum (Finset.range (N + 1))
    (fun (i : ℕ) => ∑ j ∈ Finset.range (N + 1),
      (fun x : UnitAddCircle =>
        fourierCoeff (f : UnitAddCircle → ℂ) ((i : ℤ) - (j : ℤ)) *
          fourier ((i : ℤ) - (j : ℤ)) x))
    (fun (i : ℕ) hi =>
      integrable_finsetSum' (Finset.range (N + 1)) (fun (j : ℕ) hj => hterm i j))
  rw [congrFun hout k]
  simp only [Finset.sum_apply]
  unfold circleDifferenceSum
  apply Finset.sum_congr rfl
  intro i hi
  have hin := fourierCoeff.sum (Finset.range (N + 1))
    (fun (j : ℕ) => fun x : UnitAddCircle =>
      fourierCoeff (f : UnitAddCircle → ℂ) ((i : ℤ) - (j : ℤ)) *
        fourier ((i : ℤ) - (j : ℤ)) x)
    (fun (j : ℕ) hj => hterm i j)
  rw [congrFun hin k]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fourierCoeff.const_mul]
  have he := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) ((i : ℤ) - (j : ℤ))) k
  rw [he, Pi.single_apply]
  by_cases hk : k = (i : ℤ) - (j : ℤ)
  · simp only [ite_eq_left hk, mul_one]
    exact congrArg (fourierCoeff (f : UnitAddCircle → ℂ)) hk.symm
  · simp only [ite_eq_right hk, mul_zero]

/-- **Fourier coefficient of a Fejér polynomial.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and N∈ℕ, let
F_N(f)=circleFejerPolynomial f N be the continuous Fejér polynomial (N+1)⁻¹∑_{0≤i,j≤N}
f̂(i-j)e_(i-j). Put w_N(k)=circleFejerWeight N k=(N+1-|k|)_+/(N+1), viewed as a complex
scalar, where (·)_+ is truncation at zero. For every k∈ℤ, fourierCoeff(F_N(f))
k=w_N(k)*fourierCoeff f k. Thus the coefficient is zero for |k|>N, and the zero-frequency
coefficient equals f̂(0), including N=0.
-/
theorem circleFejerPolynomial_fourierCoeff
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (N : ℕ) (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => circleFejerPolynomial f N x) k =
      circleFejerWeight N k * fourierCoeff (f : UnitAddCircle → ℂ) k := by
  rw [circleFejerPolynomial_fourierCoeff_sum]
  exact circleDifferenceSum_eq N k _

/-- **Fejér weights approach one at each fixed frequency.**

For fixed k∈ℤ and w_N(k)=(N+1-|k|)_+/(N+1)∈ℂ, circleFejerWeight N k tends to 1 as N∈ℕ tends to
infinity.
-/
theorem circleFejerWeight_tendsto (k : ℤ) :
    Tendsto (fun N : ℕ => circleFejerWeight N k) atTop (𝓝 1) := by
  have hzero : Tendsto (fun N : ℕ => (k.natAbs : ℂ) / ((N : ℂ) + 1)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => (k.natAbs : ℂ)) atTop (𝓝 (k.natAbs : ℂ)) :=
      tendsto_const_nhds
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      hconst.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))
  have ht : Tendsto (fun N : ℕ => 1 - (k.natAbs : ℂ) / ((N : ℂ) + 1)) atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 (1 : ℂ)) := tendsto_const_nhds
    simpa only [sub_zero] using hone.sub hzero
  apply ht.congr'
  filter_upwards [eventually_ge_atTop k.natAbs] with N hN
  have he : ((N + 1 - k.natAbs : ℕ) : ℂ) = (N : ℂ) + 1 - (k.natAbs : ℂ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  have hn : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  unfold circleFejerWeight
  rw [he]
  field_simp [hn]

/-- **Coefficientwise convergence of Fejér polynomials.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and N∈ℕ, let
F_N(f)=circleFejerPolynomial f N be the continuous Fejér polynomial (N+1)⁻¹∑_{0≤i,j≤N}
f̂(i-j)e_(i-j). For each fixed k∈ℤ, fourierCoeff(F_N(f)) k tends to fourierCoeff f k as N→∞.
-/
theorem circleFejerPolynomial_fourierCoeff_tendsto
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (k : ℤ) :
    Tendsto (fun N : ℕ => fourierCoeff (fun x : UnitAddCircle => circleFejerPolynomial f N x) k)
      atTop (𝓝 (fourierCoeff (f : UnitAddCircle → ℂ) k)) := by
  have ht := (circleFejerWeight_tendsto k).mul_const (fourierCoeff (f : UnitAddCircle → ℂ) k)
  apply (show Tendsto (fun N : ℕ => circleFejerWeight N k * fourierCoeff (f : UnitAddCircle → ℂ) k)
    atTop (𝓝 (fourierCoeff (f : UnitAddCircle → ℂ) k)) from by simpa only [one_mul] using ht).congr'
  exact Filter.Eventually.of_forall (fun N => (circleFejerPolynomial_fourierCoeff f N k).symm)

end MathlibExt.Analysis.Fourier
