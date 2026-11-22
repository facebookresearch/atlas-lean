/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.RingTheory.PowerSeries.Inverse

namespace MetaMathlibExt

@[expose] public section

/-- **The INVERT transform of an integer sequence.** The INVERT transform of an integer sequence
$a = (a_n)_{n \ge 0}$ is the integer sequence $b = (b_n)_{n \ge 0}$ in which $b_n$ is the
coefficient of $x^{n+1}$ in the inverse of $1 - \sum_{m \ge 0} a_m x^{m+1}$ in $\mathbb{Z}[[x]]$
(the inverse exists because the constant coefficient is $1$). In the one-based indexing of the
source, $a_n$ and $b_n$ are the terms of index $n + 1$.

Source: concept `jis_sem_22fea8fd5a269c1828606fd8`; source statements
`jis_bdc94f3dcf45a8b11a488c9a`, `jis_fa06f78544747f9465a909ce`,
`jis_a1ec2137c84e5b9b5ce1f3f7`, `jis_dc5074e4bf1c7aedd3a999d3`. -/
noncomputable def invertTransform (a : ℕ → ℤ) : ℕ → ℤ :=
  fun n => PowerSeries.coeff (n + 1) ((1 - PowerSeries.X * PowerSeries.mk a).invOfUnit 1)

/-- **Generating function of the INVERT transform.** Let $a = (a_n)_{n \ge 0}$ be an integer
sequence and $b = (b_n)_{n \ge 0}$ its INVERT transform, and put
$A(x) = \sum_{n \ge 0} a_n x^{n+1}$ and $B(x) = \sum_{n \ge 0} b_n x^{n+1}$. Then
$(1 - A(x))(1 + B(x)) = 1$ in $\mathbb{Z}[[x]]$, that is, $1 + B(x)$ is the inverse of $1 - A(x)$.

Source: concept `jis_sem_22fea8fd5a269c1828606fd8`. -/
theorem invertTransform_spec (a : ℕ → ℤ) :
    (1 - PowerSeries.X * PowerSeries.mk a) *
      (1 + PowerSeries.X * PowerSeries.mk (invertTransform a)) = 1 := by
  have hφ : PowerSeries.constantCoeff (1 - PowerSeries.X * PowerSeries.mk a) =
      ((1 : ℤˣ) : ℤ) := by
    simp
  have hC : PowerSeries.C
      (PowerSeries.constantCoeff
        ((1 - PowerSeries.X * PowerSeries.mk a).invOfUnit 1)) = 1 := by
    simp [PowerSeries.constantCoeff_invOfUnit]
  have hdecomp := PowerSeries.eq_X_mul_shift_add_const
    ((1 - PowerSeries.X * PowerSeries.mk a).invOfUnit 1)
  rw [hC] at hdecomp
  have hmk : PowerSeries.mk (invertTransform a) =
      PowerSeries.mk fun p => PowerSeries.coeff (p + 1)
        ((1 - PowerSeries.X * PowerSeries.mk a).invOfUnit 1) := rfl
  have h_eq : (1 : PowerSeries ℤ) + PowerSeries.X * PowerSeries.mk (invertTransform a)
      = (1 - PowerSeries.X * PowerSeries.mk a).invOfUnit 1 := by
    rw [hmk, add_comm]
    exact hdecomp.symm
  calc (1 - PowerSeries.X * PowerSeries.mk a) *
        (1 + PowerSeries.X * PowerSeries.mk (invertTransform a))
      = (1 - PowerSeries.X * PowerSeries.mk a) *
        ((1 - PowerSeries.X * PowerSeries.mk a).invOfUnit 1) := by
          rw [h_eq]
    _ = 1 := PowerSeries.mul_invOfUnit _ _ hφ

end

end MetaMathlibExt
