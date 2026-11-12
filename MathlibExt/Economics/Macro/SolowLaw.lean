/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Discrete Solow capital-accumulation law

Capital per effective worker is `k = K / E`. Effective labor next period is
`(1 + n) * (1 + g)` times effective labor this period (population and
technology factors multiply), and aggregate capital next period is saving
times output plus undepreciated capital. Dividing the aggregate identity by
next period's effective labor gives the per-effective-worker law. The `n * g`
term in `(1 + n) * (1 + g) = 1 + n + g + n * g` is real, not a second-order
term to drop.

## Main results

* `MathlibExt.Economics.Macro.SolowLaw.solow_law`: the discrete Solow law.
* `MathlibExt.Economics.Macro.SolowLaw.solow_effectiveLabor_factor`: the
  exact effective-labor growth factor.
* `MathlibExt.Economics.Macro.SolowLaw.solow_law_example`: a concrete
  instance giving `k' = 435/121`.

## References

Atlas roadmap target MA03.T01.
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.SolowLaw

/-- The exact discrete growth factor of effective labor. -/
theorem solow_effectiveLabor_factor (n g : ℝ) :
    (1 + n) * (1 + g) = 1 + n + g + n * g := by
  ring

/-- **Discrete Solow law.** Dividing the aggregate accumulation identity by
next period's effective labor gives the per-effective-worker law. -/
theorem solow_law {f : ℝ → ℝ} {s δ n g k k' K K' E E' F : ℝ}
    (hE : E ≠ 0) (hD : (1 + n) * (1 + g) ≠ 0)
    (hE' : E' = (1 + n) * (1 + g) * E)
    (hK' : K' = s * F + (1 - δ) * K)
    (hF : F = f k * E)
    (hk : k = K / E) (hk' : k' = K' / E') :
    k' = (s * f k + (1 - δ) * k) / ((1 + n) * (1 + g)) := by
  rw [hk', hK', hF, hk, hE']
  have h2 := mul_ne_zero hD hE
  field_simp [h2]

/-- **Concrete instance.** With `s = 1/4`, `δ = 1/10`, `n = g = 1/10`,
`f k = 3` at `k = 4`: next period's capital per effective worker is
`435/121`. -/
theorem solow_law_example {f : ℝ → ℝ} (hf : f 4 = 3) :
    ((1 / 4 : ℝ) * f 4 + (1 - 1 / 10) * 4) / ((1 + 1 / 10) * (1 + 1 / 10)) =
      435 / 121 := by
  rw [hf]
  norm_num

end MathlibExt.Economics.Macro.SolowLaw
