/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The statement is adapted from `benchmark/level2/ma_proofbench_l2_33.lean` in
openbmb/ma-proofbench at commit 31bab4c78fd1b0c464e767d62e9202163d1e9029
(MA-ProofBench, L. Pu et al., arXiv:2606.13782), previously recorded in
`WantedExt.Analysis.OperatorTheory.UnilateralShiftCharacterizationWanted`.
The ATLAS names, statements, and docstrings are retained; the proof is new.
As in the original ATLAS adaptation, `IsShift` omits the benchmark's unused `CompleteSpace`
argument. The theorem retains it.

MIT License

Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions

/-!
# Characterization of the unilateral shift

A unilateral shift is an isometry with one-dimensional range orthogonal complement and
trivial intersection of its iterated ranges. Conversely, under these conditions the orbit
of a unit vector orthogonal to the range is a Hilbert basis.
-/

namespace MathlibExt.Analysis.OperatorTheory.UnilateralShiftCharacterizationWanted

open Submodule

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem shift_coordinates (T : H →L[ℂ] H) (b : HilbertBasis ℕ ℂ H)
    (hb : ∀ n, T (b n) = b (n + 1)) :
    (∀ x, inner ℂ (b 0) (T x) = 0) ∧
      ∀ n x, inner ℂ (b (n + 1)) (T x) = inner ℂ (b n) x := by
  have hOrth := orthonormal_iff_ite.mp b.orthonormal
  have hDense : Dense (span ℂ (Set.range b) : Set H) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span
  constructor
  · have h : (innerSL ℂ (b 0)).comp T = 0 := by
      apply ContinuousLinearMap.ext_on hDense
      rintro _ ⟨i, rfl⟩
      change inner ℂ (b 0) (T (b i)) = 0
      rw [hb, hOrth]
      simp
    exact fun x ↦ congrArg (fun f : H →L[ℂ] ℂ ↦ f x) h
  · intro n
    have h : (innerSL ℂ (b (n + 1))).comp T = innerSL ℂ (b n) := by
      apply ContinuousLinearMap.ext_on hDense
      rintro _ ⟨i, rfl⟩
      change inner ℂ (b (n + 1)) (T (b i)) = inner ℂ (b n) (b i)
      rw [hb, hOrth, hOrth]
      simp
    exact fun x ↦ congrArg (fun f : H →L[ℂ] ℂ ↦ f x) h

private theorem conditions_of_basis_shift (T : H →L[ℂ] H) (b : HilbertBasis ℕ ℂ H)
    (hb : ∀ n, T (b n) = b (n + 1)) :
    (∀ x y : H, inner ℂ (T x) (T y) = inner ℂ x y) ∧
      (⨅ n : ℕ, LinearMap.range (T.toLinearMap ^ (n + 1))) = ⊥ ∧
      Module.rank ℂ (T.rangeᗮ) = 1 := by
  obtain ⟨hHead, hTail⟩ := shift_coordinates T b hb
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    -- Parseval: the zeroth coefficient vanishes and the tail is unchanged.
    rw [← b.tsum_inner_mul_inner (T x) (T y),
      (b.summable_inner_mul_inner (T x) (T y)).tsum_eq_zero_add]
    rw [hHead, mul_zero, zero_add, ← b.tsum_inner_mul_inner x y]
    refine tsum_congr fun n ↦ ?_
    rw [hTail, ← inner_conj_symm (T x) (b (n + 1)), hTail, inner_conj_symm]
  · have hPow : ∀ n x, inner ℂ (b n) ((T.toLinearMap ^ (n + 1)) x) = 0 := by
      intro n
      induction n with
      | zero =>
        intro x
        rw [Nat.zero_add, pow_one]
        exact hHead x
      | succ n ih =>
        intro x
        rw [pow_succ']
        change inner ℂ (b (n + 1)) (T ((T.toLinearMap ^ (n + 1)) x)) = 0
        rw [hTail]
        exact ih x
    refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ b.repr.injective ?_
    ext n
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp ((Submodule.mem_iInf _).mp hx n)
    simp [b.repr_apply_apply, hPow]
  · have hRange : T.rangeᗮ = ℂ ∙ b 0 := by
      refine le_antisymm (fun x hx ↦ ?_) ?_
      · have hBasis (n : ℕ) : b (n + 1) ∈ T.range := ⟨b n, hb n⟩
        have hCoeff (n : ℕ) : inner ℂ (b (n + 1)) x = 0 :=
          inner_right_of_mem_orthogonal (hBasis n) hx
        refine Submodule.mem_span_singleton.mpr ⟨inner ℂ (b 0) x, b.repr.injective ?_⟩
        ext n
        simp only [b.repr_apply_apply, inner_smul_right]
        cases n with
        | zero => simp [b.orthonormal.norm_eq_one]
        | succ n => simp [orthonormal_iff_ite.mp b.orthonormal, hCoeff n]
      · apply Submodule.span_le.mpr
        apply Set.singleton_subset_iff.mpr
        apply (T.range.mem_orthogonal' _).mpr
        rintro _ ⟨x, rfl⟩
        exact hHead x
    rw [hRange, Module.rank_eq_one_iff_finrank_eq_one]
    exact finrank_span_singleton (b.orthonormal.ne_zero 0)

private theorem exists_unit_defect_vector (T : H →L[ℂ] H)
    (hDim : Module.rank ℂ (T.rangeᗮ) = 1) :
    ∃ e : H, ‖e‖ = 1 ∧ e ∈ T.rangeᗮ ∧ T.rangeᗮ = ℂ ∙ e := by
  let : FiniteDimensional ℂ (T.rangeᗮ) := Module.finite_of_rank_eq_one hDim
  let b := (stdOrthonormalBasis ℂ (T.rangeᗮ)).reindex
    (finCongr (Module.rank_eq_one_iff_finrank_eq_one.mp hDim))
  refine ⟨b 0, b.orthonormal.norm_eq_one 0, (b 0).property, ?_⟩
  refine le_antisymm (fun x hx ↦ ?_)
    (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (b 0).property))
  let y : T.rangeᗮ := ⟨x, hx⟩
  refine Submodule.mem_span_singleton.mpr ⟨b.repr y 0, ?_⟩
  have hy := b.sum_repr y
  rw [Fin.sum_univ_one] at hy
  exact congrArg Subtype.val hy

private theorem basis_shift_of_conditions [CompleteSpace H] (T : H →L[ℂ] H)
    (hIso : ∀ x y : H, inner ℂ (T x) (T y) = inner ℂ x y)
    (hPure : (⨅ n : ℕ, LinearMap.range (T.toLinearMap ^ (n + 1))) = ⊥)
    (hDim : Module.rank ℂ (T.rangeᗮ) = 1) :
    ∃ b : HilbertBasis ℕ ℂ H, ∀ n : ℕ, T (b n) = b (n + 1) := by
  let U : H →ₗᵢ[ℂ] H := ⟨T.toLinearMap, (LinearMap.norm_map_iff_inner_map_map T).mpr hIso⟩
  have : IsClosed (T.range : Set H) := U.isometry.isClosedEmbedding.isClosed_range
  let : CompleteSpace T.range := IsClosed.completeSpace_coe
  obtain ⟨e, heNorm, heOrth, heSpan⟩ := exists_unit_defect_vector T hDim
  let v : ℕ → H := fun n ↦ (T.toLinearMap ^ n) e
  have hvZero : v 0 = e := rfl
  have hvSucc (n : ℕ) : v (n + 1) = T (v n) := by
    unfold v
    rw [pow_succ']
    rfl
  have hvRange (n : ℕ) : T (v n) ∈ T.range := ⟨v n, rfl⟩
  have hvOrth : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i
    induction i with
    | zero =>
      intro j
      cases j with
      | zero => simp [hvZero, inner_self_eq_norm_sq_to_K, heNorm]
      | succ j =>
        rw [hvZero, hvSucc]
        simpa using inner_left_of_mem_orthogonal (hvRange j) heOrth
    | succ i ih =>
      intro j
      cases j with
      | zero =>
        rw [hvZero, hvSucc]
        simpa using inner_right_of_mem_orthogonal (hvRange i) heOrth
      | succ j => simpa only [hvSucc, hIso, Nat.succ.injEq] using ih j
  have hTotal : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_
    have hCoeff (n : ℕ) : inner ℂ (v n) x = 0 :=
      inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self n)) hx
    -- An orthogonal vector has a preimage that remains orthogonal to the orbit.
    have hPreimage (z : H) (hz : ∀ n, inner ℂ (v n) z = 0) :
        ∃ y, T y = z ∧ ∀ n, inner ℂ (v n) y = 0 := by
      have hzRange : z ∈ T.range := by
        rw [← Submodule.orthogonal_orthogonal T.range, heSpan,
          Submodule.mem_orthogonal_singleton_iff_inner_right, ← hvZero]
        exact hz 0
      obtain ⟨y, rfl⟩ := (show ∃ y, T y = z from hzRange)
      refine ⟨y, rfl, fun n ↦ ?_⟩
      simpa only [hvSucc, hIso] using hz (n + 1)
    have hPow (n : ℕ) (z : H) (hz : ∀ m, inner ℂ (v m) z = 0) :
        z ∈ LinearMap.range (T.toLinearMap ^ n) := by
      induction n generalizing z with
      | zero => exact ⟨z, rfl⟩
      | succ n ih =>
        obtain ⟨y, rfl, hy⟩ := hPreimage z hz
        obtain ⟨w, hw⟩ := ih y hy
        refine ⟨w, ?_⟩
        rw [pow_succ']
        change T ((T.toLinearMap ^ n) w) = T y
        rw [hw]
    have hxRange : x ∈ ⨅ n : ℕ, LinearMap.range (T.toLinearMap ^ (n + 1)) :=
      (Submodule.mem_iInf _).mpr fun n ↦ hPow (n + 1) x hCoeff
    simpa [hPure] using hxRange
  refine ⟨HilbertBasis.mkOfOrthogonalEqBot hvOrth hTotal, fun n ↦ ?_⟩
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  exact (hvSucc n).symm

end

@[expose] public section

/-- **Unilateral shift operator.** A bounded linear operator $T$ on a complex inner product
space $H$ is a unilateral shift if there is a Hilbert basis $(b_n)_{n \in \mathbb{N}}$ of $H$
such that $T b_n = b_{n+1}$ for every $n \in \mathbb{N}$. -/
def IsShift
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) : Prop :=
  ∃ b : HilbertBasis ℕ ℂ H, ∀ n : ℕ, T (b n) = b (n + 1)

/-- **Isometric characterization of the unilateral shift.** Let $H$ be a separable complex
Hilbert space, and call a bounded linear operator $T : H \to H$ a shift if there is an
orthonormal basis $(e_n)_{n \in \mathbb{N}}$ of $H$ with $T e_n = e_{n+1}$ for every
$n \in \mathbb{N}$. Then a bounded linear operator $T : H \to H$ is a shift if and only if the
following three conditions hold: $T$ is an isometry, that is,
$\langle T x, T y \rangle = \langle x, y \rangle$ for all $x, y \in H$; the ranges of the powers
of $T$ satisfy $\bigcap_{n \ge 1} \mathrm{Ran}(T^n) = \{0\}$; and the orthogonal complement
$(\mathrm{Ran}\, T)^\perp$ of the range of $T$ has dimension $1$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Special
classes of linear operators), `benchmark/level2/ma_proofbench_l2_33.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem isShift_iff_isometry_iInf_range_pow_eq_bot_finrank_orthogonal_eq_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (T : H →L[ℂ] H) :
    IsShift T ↔
      (∀ x y : H, inner ℂ (T x) (T y) = inner ℂ x y) ∧
        (⨅ n : ℕ, LinearMap.range (T.toLinearMap ^ (n + 1))) = ⊥ ∧
        Module.rank ℂ (T.rangeᗮ) = 1 := by
  constructor
  · rintro ⟨b, hb⟩
    exact conditions_of_basis_shift T b hb
  · rintro ⟨hIso, hPure, hDim⟩
    exact basis_shift_of_conditions T hIso hPure hDim

end

end MathlibExt.Analysis.OperatorTheory.UnilateralShiftCharacterizationWanted
