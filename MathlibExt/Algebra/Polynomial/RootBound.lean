/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.L1Norm
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Normed.Ring.WithAbs

/-!
# Root bound via the L1 norm

A root of a monic polynomial is strictly bounded by the L1 norm of the
polynomial, provided the absolute value on the root's field restricts to the
absolute value on the coefficient field.
-/

@[expose] public section

namespace Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)
  [AbsoluteValue.LiesOver w v]

/-- **Root bound by the L1 norm.** Let $K$ and $L$ be fields with $L$ a $K$-algebra, let $v$ be a
real-valued absolute value on $K$, and let $w$ be a real-valued absolute value on $L$ lying over
$v$, that is, $w(x) = v(x)$ for every $x \in K$ viewed in $L$ through the algebra map. If $f$ is a
monic polynomial over $K$ and $\alpha \in L$ is a root of $f$, then $w(\alpha)$ is strictly less
than the L1 norm of $f$ with respect to $v$.

No algebraicity, finiteness, completeness, or archimedean hypothesis is needed. -/
theorem aeval_lt_l1Norm_of_monic_of_aeval_eq_zero {f : Polynomial K}
    (hf : f.Monic) {α : L} (hroot : aeval α f = 0) :
    w α < l1Norm v f := by
  have hcompat : ∀ x : K, w (algebraMap K L x) = v x := fun x =>
    DFunLike.congr_fun (AbsoluteValue.LiesOver.comp_eq w v) x
  rcases lt_or_ge (w α) 1 with hsmall | hbig
  · exact hsmall.trans_le (one_le_l1Norm_of_monic v f hf)
  · have hroot2 : eval₂ (algebraMap K L) α f = 0 := by
      rwa [← aeval_def]
    rw [eval₂_eq_sum_range, Finset.sum_range_succ] at hroot2
    have hlead : algebraMap K L (f.coeff f.natDegree) * α ^ f.natDegree
        = α ^ f.natDegree := by
      rw [hf.coeff_natDegree, map_one, one_mul]
    rw [hlead] at hroot2
    have hpow : α ^ f.natDegree
        = -∑ i ∈ Finset.range f.natDegree,
          algebraMap K L (f.coeff i) * α ^ i :=
      eq_neg_of_add_eq_zero_right hroot2
    have htriangle : w α ^ f.natDegree
        ≤ ∑ i ∈ Finset.range f.natDegree, v (f.coeff i) * w α ^ i := by
      calc w α ^ f.natDegree = w (α ^ f.natDegree) :=
            (AbsoluteValue.map_pow w α f.natDegree).symm
        _ = w (∑ i ∈ Finset.range f.natDegree,
            algebraMap K L (f.coeff i) * α ^ i) := by
          rw [hpow, AbsoluteValue.map_neg]
        _ ≤ ∑ i ∈ Finset.range f.natDegree,
            w (algebraMap K L (f.coeff i) * α ^ i) :=
          AbsoluteValue.sum_le w _ _
        _ = ∑ i ∈ Finset.range f.natDegree, v (f.coeff i) * w α ^ i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [AbsoluteValue.map_mul w _ _, AbsoluteValue.map_pow w _ _,
            hcompat]
    have hsum : ∑ i ∈ Finset.range f.natDegree, v (f.coeff i) * w α ^ i
        ≤ (∑ i ∈ Finset.range f.natDegree, v (f.coeff i))
          * w α ^ (f.natDegree - 1) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (v.nonneg _)
      apply pow_le_pow_right₀ hbig
      have := Finset.mem_range.mp hi
      omega
    have hmain : w α ^ f.natDegree
        ≤ (∑ i ∈ Finset.range f.natDegree, v (f.coeff i))
          * w α ^ (f.natDegree - 1) :=
      htriangle.trans hsum
    rcases Nat.eq_zero_or_pos f.natDegree with hzero | hpos
    · rw [hzero] at hmain
      simp at hmain
      linarith
    · have hposW : 0 < w α := lt_of_lt_of_le zero_lt_one hbig
      have hpow_pos : 0 < w α ^ (f.natDegree - 1) := pow_pos hposW _
      have hsplit : w α ^ f.natDegree
          = w α ^ (f.natDegree - 1) * w α := by
        conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ f.natDegree from hpos),
          pow_succ]
      have hle_S : w α ≤ ∑ i ∈ Finset.range f.natDegree, v (f.coeff i) :=
        le_of_mul_le_mul_left (by
          rw [← hsplit, mul_comm (w α ^ (f.natDegree - 1))]
          exact hmain) hpow_pos
      have hL1 := l1Norm_eq_sum_range_add_one_of_monic v f hf
      rw [hL1]
      linarith

end Polynomial

