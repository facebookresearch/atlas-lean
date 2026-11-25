/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Shared tools for contraction limits of polynomial-preserving chains

This file contains the generic analytic facts used to extend finite-chain limits from a dense set
to all continuous functions. It also records that powers of a positive unital continuous linear
endomorphism remain positive and unital.

The Wright–Fisher neutral semigroup and its mutation extension use these results with polynomial
functions on `[0, 1]`. Polynomial embeddings themselves use Mathlib's canonical
`Polynomial.toContinuousMapOnAlgHom`; no wrapper is introduced here. No semigroup is defined here.

The available equicontinuity extension route assumes equicontinuity. The arguments below instead
derive convergence from a uniform operator-norm contraction bound and convergence on a dense set.
-/

@[expose] public section

open Filter Polynomial Topology
open scoped unitInterval

namespace MathlibExt.Biology.PopulationGenetics.Diffusion.ChainLimit

/-- Uniformly contractive operators that are Cauchy on a dense set are Cauchy everywhere. -/
theorem cauchySeq_apply_of_dense {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℕ → E →L[ℝ] E} (hL : ∀ M, ‖L M‖ ≤ 1) {D : Set E}
    (hD : Dense D) (h : ∀ d ∈ D, CauchySeq fun M => L M d) (f : E) :
    CauchySeq fun M => L M f := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨d, hd, hfd⟩ := hD.exists_dist_lt f hε3
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (h d hd) (ε / 3) hε3
  have hdist (M : ℕ) : dist (L M f) (L M d) ≤ dist f d := by
    simpa only [dist_eq_norm, ← map_sub, one_mul] using
      (L M).le_of_opNorm_le (hL M) (f - d)
  refine ⟨N, ?_⟩
  intro M hM P hP
  have hmid := hN M hM P hP
  have hlast : dist (L P d) (L P f) ≤ dist f d := by
    rw [dist_comm]
    exact hdist P
  have htri := dist_triangle4 (L M f) (L M d) (L P d) (L P f)
  linarith [hdist M]

/-- Limits of uniformly contractive operators extend from a dense set to the whole space. -/
theorem tendsto_apply_of_dense {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} {l : Filter ι} {T : ι → E →L[ℝ] E}
    (hT : ∀ i, ‖T i‖ ≤ 1) {S : E →L[ℝ] E} (hS : ‖S‖ ≤ 1) {D : Set E}
    (hD : Dense D) (h : ∀ d ∈ D, Tendsto (fun i => T i d) l (𝓝 (S d))) (f : E) :
    Tendsto (fun i => T i f) l (𝓝 (S f)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨d, hd, hfd⟩ := hD.exists_dist_lt f hε3
  have hdist (i : ι) : dist (T i f) (T i d) ≤ dist f d := by
    simpa only [dist_eq_norm, ← map_sub, one_mul] using
      (T i).le_of_opNorm_le (hT i) (f - d)
  have hlast : dist (S d) (S f) ≤ dist f d := by
    simpa only [dist_eq_norm, ← map_sub, one_mul, norm_sub_rev] using
      S.le_of_opNorm_le hS (d - f)
  apply (Metric.tendsto_nhds.mp (h d hd) (ε / 3) hε3).mono
  intro i hi
  have htri := dist_triangle4 (T i f) (T i d) (S d) (S f)
  linarith [hdist i]

/-- Weierstrass approximation: polynomial functions are dense in `C([0, 1], ℝ)`. -/
theorem dense_polynomialFunctions : Dense (polynomialFunctions I : Set C(I, ℝ)) := by
  rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe,
    polynomialFunctions_closure_eq_top']
  rfl

/-- If `t ≤ 0`, then the natural floor of `t * M` is zero. -/
theorem floor_mul_eq_zero {t : ℝ} (ht : t ≤ 0) (M : ℕ) : ⌊t * M⌋₊ = 0 :=
  Nat.floor_of_nonpos (mul_nonpos_of_nonpos_of_nonneg ht (Nat.cast_nonneg M))

end MathlibExt.Biology.PopulationGenetics.Diffusion.ChainLimit

namespace ContinuousLinearMap

/-- Every power of a continuous linear endomorphism fixing `1` also fixes `1`. -/
theorem pow_apply_one {R E : Type*} [Semiring R] [TopologicalSpace E] [AddCommMonoid E]
    [Module R E] [One E] (T : E →L[R] E) (hT : T 1 = 1) (n : ℕ) :
    (T ^ n) 1 = 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_apply_eq_comp, hT, ih]

/-- Every power of a positive continuous linear endomorphism is positive. -/
theorem pow_nonneg {R E : Type*} [Semiring R] [TopologicalSpace E] [AddCommMonoid E]
    [Module R E] [PartialOrder E] (T : E →L[R] E)
    (hT : ∀ {f : E}, 0 ≤ f → 0 ≤ T f) (n : ℕ) {f : E} (hf : 0 ≤ f) :
    0 ≤ (T ^ n) f := by
  induction n with
  | zero => simpa
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact hT ih

end ContinuousLinearMap
