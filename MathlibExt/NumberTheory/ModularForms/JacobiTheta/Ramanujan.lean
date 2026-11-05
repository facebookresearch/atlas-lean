/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.LinearAlgebra.Complex.FiniteDimensional

public import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Ring

/-!
# Ramanujan's general theta function

This file defines Ramanujan's general theta function in its two multiplicative parameters

  `f(a,b) = ∑_{n ∈ ℤ} a ^ (n * (n + 1) / 2) * b ^ (n * (n - 1) / 2)`,

with classical (absolute) convergence on `‖a * b‖ < 1`. The raw sum
`ramanujanThetaRaw` is Mathlib's total `tsum`, which is `0` for a nonsummable family.
The canonical `ramanujanTheta` therefore requires an explicit summability witness.

## Main definitions

* `ramanujanThetaTerm a b n` — the `n`th summand.
* `ramanujanThetaRaw a b` — the unrestricted total `tsum`.
* `ramanujanTheta a b h` — the theta sum with summability evidence `h`.

## Main results

* `ramanujanThetaTerm_neg` and `ramanujanTheta_symm`: `f(a,b) = f(b,a)` via `n ↦ -n`.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Summand of Ramanujan's general theta function.** For complex numbers $a$, $b$ and an
integer $n$, this is the term $a^{n(n+1)/2} b^{n(n-1)/2}$ of index $n$ in Ramanujan's general
theta function $f(a,b) = \sum_{k \in \mathbb{Z}} a^{k(k+1)/2} b^{k(k-1)/2}$.

Both exponents $n(n+1)/2$ and $n(n-1)/2$ are nonnegative integers for every integer $n$, so
the term is a product of ordinary powers with natural-number exponents.

Source: the common definition in arXiv:2305.14988,
arXiv:2309.06689, arXiv:2312.15513, arXiv:2502.17312, and arXiv:2607.26471. -/
noncomputable def ramanujanThetaTerm (a b : ℂ) (n : ℤ) : ℂ :=
  a ^ (n * (n + 1) / 2).toNat * b ^ (n * (n - 1) / 2).toNat

/-- **Raw Ramanujan theta sum.** For complex numbers $a$ and $b$, the raw Ramanujan theta sum is
$\sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ when this series is summable, and $0$
otherwise.

The value $0$ for a non-summable series is a convention. Ramanujan's general theta function,
which requires the series to be summable, is the intended object. -/
noncomputable def ramanujanThetaRaw (a b : ℂ) : ℂ :=
  ∑' n : ℤ, ramanujanThetaTerm a b n

/-- **Ramanujan's general theta function.** For complex numbers $a$ and $b$ such that the series
$\sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ is summable, Ramanujan's general theta
function is its sum $f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$. -/
noncomputable def ramanujanTheta (a b : ℂ)
    (_h : Summable (ramanujanThetaTerm a b)) : ℂ :=
  ramanujanThetaRaw a b

@[simp]
theorem ramanujanThetaTerm_zero (a b : ℂ) :
    ramanujanThetaTerm a b 0 = 1 := by
  simp [ramanujanThetaTerm]

@[simp]
theorem ramanujanThetaTerm_one (a b : ℂ) :
    ramanujanThetaTerm a b 1 = a := by
  simp [ramanujanThetaTerm]

@[simp]
theorem ramanujanThetaTerm_neg_one (a b : ℂ) :
    ramanujanThetaTerm a b (-1) = b := by
  simp [ramanujanThetaTerm]

theorem ramanujanThetaTerm_neg (a b : ℂ) (n : ℤ) :
    ramanujanThetaTerm a b (-n) = ramanujanThetaTerm b a n := by
  unfold ramanujanThetaTerm
  have h₁ : (-n) * (-n + 1) / (2 : ℤ) = n * (n - 1) / 2 := by
    rw [show (-n) * (-n + 1) = n * (n - 1) by ring]
  have h₂ : (-n) * (-n - 1) / (2 : ℤ) = n * (n + 1) / 2 := by
    rw [show (-n) * (-n - 1) = n * (n + 1) by ring]
  rw [h₁, h₂, mul_comm]

theorem ramanujanTheta_summable_symm (a b : ℂ) :
    Summable (ramanujanThetaTerm a b) ↔ Summable (ramanujanThetaTerm b a) := by
  constructor
  · intro hab
    have h := (Equiv.neg ℤ).summable_iff.mpr hab
    simpa [Function.comp_def, ramanujanThetaTerm_neg] using h
  · intro hba
    have h := (Equiv.neg ℤ).summable_iff.mpr hba
    simpa [Function.comp_def, ramanujanThetaTerm_neg] using h

theorem ramanujanThetaRaw_symm (a b : ℂ) :
    ramanujanThetaRaw a b = ramanujanThetaRaw b a := by
  unfold ramanujanThetaRaw
  have h : ∀ n : ℤ, ramanujanThetaTerm a b n = ramanujanThetaTerm b a (-n) :=
    fun n => (ramanujanThetaTerm_neg b a n).symm
  calc
    ∑' n : ℤ, ramanujanThetaTerm a b n =
        ∑' n : ℤ, ramanujanThetaTerm b a (-n) := by simp_rw [h]
    _ = ∑' n : ℤ, ramanujanThetaTerm b a n :=
      Equiv.tsum_eq (Equiv.neg ℤ) (fun n => ramanujanThetaTerm b a n)

theorem ramanujanTheta_symm (a b : ℂ) (h : Summable (ramanujanThetaTerm a b)) :
    ramanujanTheta a b h =
      ramanujanTheta b a ((ramanujanTheta_summable_symm a b).mp h) := by
  simpa [ramanujanTheta] using ramanujanThetaRaw_symm a b

/-- **Ramanujan's theta series diverges at $a = b = 1$.** The series
$\sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ of Ramanujan's general theta function is
not summable at $a = b = 1$, since every one of its terms equals $1$. -/
theorem not_summable_ramanujanThetaTerm_one_one :
    ¬Summable (ramanujanThetaTerm 1 1) := by
  intro h
  have hnorm : Summable (fun _ : ℤ => (1 : ℝ)) := by
    simpa [ramanujanThetaTerm] using h.norm
  exact @not_finite ℤ inferInstance (Finite.of_summable_const zero_lt_one hnorm)

/-- **The raw Ramanujan theta sum vanishes at $a = b = 1$.** The raw Ramanujan theta sum
$\sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$, which is assigned the value $0$ whenever
the series is not summable, equals $0$ at $a = b = 1$, because there every term equals $1$ and
the series is not summable. -/
theorem ramanujanThetaRaw_one_one : ramanujanThetaRaw 1 1 = 0 := by
  exact tsum_eq_zero_of_not_summable not_summable_ramanujanThetaTerm_one_one

end MetaMathlibExt
