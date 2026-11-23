/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic

/-!
# Real exchange-rate conversion

Under the frozen quote convention — `E` is domestic currency per unit of
foreign currency, `P*` the foreign price index, `P` the domestic price
index — the foreign basket costs `E * P*` in domestic currency, and the
real exchange rate is `q = E * P* / P` (domestic baskets per foreign
basket). The conversion formula is `q * P = E * P*`. No claim is made about
purchasing-power parity (`q = 1`), about `E` being market-determined, or
about the formula under the opposite quotation.

## Main results

* `realExchangeRate_mul_price`: the conversion formula.
* `realExchangeRate_eq_nominal_div_priceRatio`: `q = E / (P / P*)`.
* `realExchangeRate_strictMono_nominal`: a higher `E` (domestic depreciation) raises `q`.

## References

* N. G. Mankiw, *Macroeconomics*, Worth Publishers, chapter on the open
  economy (real exchange rate).

Atlas roadmap target MA05.T04.
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.RealExchangeRate

/-- Real exchange rate `q = E * P* / P`, under the FROZEN quote convention:
`E` is domestic currency per unit of foreign currency, `P*` the foreign price
index (foreign currency per foreign basket), `P` the domestic price index
(domestic currency per domestic basket). So `q` is domestic baskets per
foreign basket (source clause: "real exchange-rate conversion formula"). -/
noncomputable def realExchangeRate (E Pstar P : ℝ) : ℝ :=
  E * Pstar / P

/-- **Conversion formula.** The foreign basket costs `E * P*` in domestic
currency, and `q * P = E * P*`: multiplying the real rate by the domestic
price level converts back to the domestic-currency cost of the foreign basket
(Atlas roadmap MA05.T04). -/
theorem realExchangeRate_mul_price (E Pstar P : ℝ) (hP : P ≠ 0) :
    realExchangeRate E Pstar P * P = E * Pstar := by
  unfold realExchangeRate
  field_simp

/-- **Price-ratio form.** Under the same quote convention,
`q = E / (P / P*)`: the real rate is the nominal rate divided by the
domestic-to-foreign price ratio. -/
theorem realExchangeRate_eq_nominal_div_priceRatio (E Pstar P : ℝ) (hP : P ≠ 0)
    (hPs : Pstar ≠ 0) :
    realExchangeRate E Pstar P = E / (P / Pstar) := by
  unfold realExchangeRate
  field_simp

/-- **A higher nominal rate raises the real rate at fixed prices** (a higher
`E` is more domestic currency per unit of foreign currency, i.e. a
depreciation of the domestic currency). For
`P* > 0`, `P > 0`, `E₁ < E₂` implies `q(E₁) < q(E₂)`. -/
theorem realExchangeRate_strictMono_nominal (Pstar P : ℝ) (hPs : 0 < Pstar)
    (hP : 0 < P) {E1 E2 : ℝ} (hE : E1 < E2) :
    realExchangeRate E1 Pstar P < realExchangeRate E2 Pstar P := by
  unfold realExchangeRate
  gcongr

end MathlibExt.Economics.Macro.RealExchangeRate
