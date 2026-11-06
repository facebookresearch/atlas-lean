/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Simsek numbers.** For natural numbers $n$ and $k$ and a complex number $\lambda$, the Simsek
number $y_1(n, k; \lambda)$ is the complex number
$$y_1(n, k; \lambda) = \frac{1}{k!} \sum_{j=0}^{k} \binom{k}{j} j^n \lambda^j,$$
where $0^0 = 1$.

Source: equation (snmf1) of https://cs.uwaterloo.ca/journals/JIS/VOL26/Oussi/oussi9.tex;
phrase concept `jis_term_8eae8e670c41baff4a5d1101`,
semantic concept `jis_sem_cadb2d3c6cc457809c98725c`,
source statement `jis_018cebafcc5d365ff500f619`. -/
public noncomputable def simsekNumber (n k : Nat) (lam : ℂ) : ℂ :=
  ((k.factorial : ℂ))⁻¹ *
    ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * (((j : ℂ) ^ n) * (lam ^ j))

/-- **Finite-sum formula for Simsek numbers.** For all natural numbers $n$ and $k$ and every
complex number $\lambda$, the Simsek number satisfies
$y_1(n, k; \lambda) = \frac{1}{k!} \sum_{j=0}^{k} \binom{k}{j} j^n \lambda^j$, where $0^0 = 1$. -/
public theorem simsekNumber_eq_sum (n k : Nat) (lam : ℂ) :
    simsekNumber n k lam =
      ((k.factorial : ℂ))⁻¹ *
        ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * (((j : ℂ) ^ n) * (lam ^ j)) :=
  rfl

/-- **Simsek numbers with second index zero.** For every natural number $n$ and every complex
number $\lambda$, the Simsek number $y_1(n, 0; \lambda)$ equals $0^n$; that is, it equals $1$
when $n = 0$ and $0$ otherwise. -/
public theorem simsekNumber_zero_k (n : Nat) (lam : ℂ) :
    simsekNumber n 0 lam = (0 : ℂ) ^ n := by
  unfold simsekNumber
  simp

/-- **Simsek numbers with both indices zero.** For every complex number $\lambda$, the Simsek
number $y_1(0, 0; \lambda)$ equals $1$. -/
public theorem simsekNumber_zero_zero (lam : ℂ) :
    simsekNumber 0 0 lam = 1 := by
  unfold simsekNumber
  simp

end

end MetaMathlibExt
