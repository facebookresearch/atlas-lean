/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- **Terms of the modified Bessel series.** For natural numbers $m, k$ and a real number $x$, the
$k$-th term of the series for the modified Bessel function of the first kind of order $m$ is
$x^{2k+m} / (2^{2k+m} \, k! \, (k+m)!)$.

Source: concept `jis_sem_78bf9131cc4a7a0691426bd9`, clause `term`; source statements
`jis_3a038c4cc84dc07fe8919282`, `jis_7cc9c1f18e5df469ed601556`,
`jis_e0a513b24ce72583486f4f92`, `jis_f7e9efe0d7b39afbda3962c6`. -/
noncomputable def modifiedBesselI_term (m k : ℕ) (x : ℝ) : ℝ :=
  x ^ (2 * k + m) /
    ((2 : ℝ) ^ (2 * k + m) * (Nat.factorial k : ℝ) * (Nat.factorial (k + m) : ℝ))

/-- **Modified Bessel function of the first kind.** For a natural number $m$ and real $x$, the
modified Bessel function of the first kind of order $m$ is
$I_m(x) = \sum_{k \ge 0} x^{2k+m} / (2^{2k+m} \, k! \, (k+m)!)$.

Source: concept `jis_sem_78bf9131cc4a7a0691426bd9`, clause `definition`; source statements
`jis_3a038c4cc84dc07fe8919282`, `jis_7cc9c1f18e5df469ed601556`,
`jis_e0a513b24ce72583486f4f92`, `jis_f7e9efe0d7b39afbda3962c6`. -/
noncomputable def modifiedBesselI (m : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, modifiedBesselI_term m k x

/-- **Modified Bessel function of the first kind of order zero.** For a real number $x$, $I_0(x)$
is the modified Bessel function of the first kind of order $0$ at $x$, that is,
$I_0(x) = \sum_{k \ge 0} x^{2k} / (2^{2k} \, (k!)^2)$.

Source: concept `jis_sem_78bf9131cc4a7a0691426bd9`, clause `zero_order`; source statements
`jis_3a038c4cc84dc07fe8919282`, `jis_7cc9c1f18e5df469ed601556`,
`jis_e0a513b24ce72583486f4f92`, `jis_f7e9efe0d7b39afbda3962c6`. -/
noncomputable def modifiedBesselI_zero (x : ℝ) : ℝ :=
  modifiedBesselI 0 x

/-- **Modified Bessel function of the first kind of order one.** For a real number $x$, $I_1(x)$
is the modified Bessel function of the first kind of order $1$ at $x$, that is,
$I_1(x) = \sum_{k \ge 0} x^{2k+1} / (2^{2k+1} \, k! \, (k+1)!)$.

Source: concept `jis_sem_78bf9131cc4a7a0691426bd9`, clause `one_order`; source statements
`jis_3a038c4cc84dc07fe8919282`, `jis_7cc9c1f18e5df469ed601556`,
`jis_e0a513b24ce72583486f4f92`, `jis_f7e9efe0d7b39afbda3962c6`. -/
noncomputable def modifiedBesselI_one (x : ℝ) : ℝ :=
  modifiedBesselI 1 x

end

end MetaMathlibExt
