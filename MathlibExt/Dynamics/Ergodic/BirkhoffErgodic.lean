/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Dynamics.Ergodic.KingmanSigned.BirkhoffPointwise

/-!
# Birkhoff averages as explicit averages

The real Birkhoff average `birkhoffAverage ℝ T f n x` is the explicit average
`n⁻¹ ∑_{k<n} f (T^[k] x)` (`StatMech.BirkhoffAE.birkhoffAverage_eq_inv_mul_sum`). Rewriting with it
reads Birkhoff's ergodic theorem for ergodic maps,
`MathlibExt.Dynamics.Ergodic.BirkhoffWanted.birkhoff_pointwise_ergodic`, and its pointwise limit
form `StatMech.BirkhoffAE.birkhoffLimit_ae_eq_integral_of_ergodic` (from
`MathlibExt.Dynamics.Ergodic.KingmanSigned.BirkhoffPointwise`) for the explicit averages.

## Main results

* `StatMech.BirkhoffAE.birkhoffAverage_eq_inv_mul_sum`:
  `birkhoffAverage ℝ T f n x = n⁻¹ ∑_{k<n} f (T^[k] x)`.

## References

* G. D. Birkhoff, *Proof of the ergodic theorem*, Proc. Natl. Acad. Sci. USA 17 (1931), 656–660.
-/

@[expose] public section

open Finset

namespace StatMech

namespace BirkhoffAE

variable {α : Type*}

/-- The real Birkhoff average `birkhoffAverage ℝ T f n x` is the explicit average
`n⁻¹ ∑_{k<n} f (T^[k] x)`. -/
theorem birkhoffAverage_eq_inv_mul_sum (T : α → α) (f : α → ℝ) (n : ℕ) (x : α) :
    birkhoffAverage ℝ T f n x = (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f (T^[k] x) := by
  simp [birkhoffAverage, birkhoffSum, smul_eq_mul]

end BirkhoffAE

end StatMech
