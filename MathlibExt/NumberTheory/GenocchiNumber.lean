/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Exp

namespace MetaMathlibExt

@[expose] public section

/-- **Generating function of the Genocchi numbers.** The Genocchi power series is the formal power
series $\frac{2x}{e^x + 1} = 2x \cdot (e^x + 1)^{-1}$ in $\mathbb{Q}[[x]]$, where
$e^x = \sum_{n \ge 0} x^n / n!$ is the exponential power series and $(e^x + 1)^{-1}$ is the inverse
of $e^x + 1$ among formal power series. It is the exponential generating function of the Genocchi
numbers $G_n$, that is, $\frac{2x}{e^x + 1} = \sum_{n \ge 0} G_n \frac{x^n}{n!}$.

This retains the standard convention $\frac{2x}{e^x + 1}$ stated by Chen and used independently by
Kida; the sign-changed variant consumes only even-index terms, where the conventions agree.

Source: Provenance:
- phrase concept `jis_term_2151ebeb03d46b7f51d94f94`
- source statements `jis_21afe12570e34775c299908d` and `jis_5d32bc9f1d45c583ec9b9547`
- Chen, JIS VOL6 (`JIS VOL6/Chen/chen50.tex`, lines 296-300, duplicated in
  `chen53.tex`): https://cs.uwaterloo.ca/journals/JIS/VOL6/Chen/chen50.html
- Kida, JIS VOL16 (`JIS VOL16/Kida/kida2.tex`):
  https://cs.uwaterloo.ca/journals/JIS/VOL16/Kida/kida2.html -/
public noncomputable def genocchiPowerSeries : PowerSeries ℚ :=
  2 * PowerSeries.X * (PowerSeries.exp ℚ + 1)⁻¹

/-- **Genocchi numbers.** For a natural number $n$, the Genocchi number $G_n \in \mathbb{Q}$ is
$n!$ times the coefficient of $x^n$ in the Genocchi power series
$\frac{2x}{e^x + 1} \in \mathbb{Q}[[x]]$, so that
$\frac{2x}{e^x + 1} = \sum_{n \ge 0} G_n \frac{x^n}{n!}$.

Source: Provenance:
- phrase concept `jis_term_2151ebeb03d46b7f51d94f94`
- source statements `jis_21afe12570e34775c299908d` and `jis_5d32bc9f1d45c583ec9b9547`
- Chen, JIS VOL6 (`JIS VOL6/Chen/chen50.tex`, lines 296-300, duplicated in
  `chen53.tex`): https://cs.uwaterloo.ca/journals/JIS/VOL6/Chen/chen50.html
- Kida, JIS VOL16 (`JIS VOL16/Kida/kida2.tex`):
  https://cs.uwaterloo.ca/journals/JIS/VOL16/Kida/kida2.html -/
public noncomputable def genocchiNumber (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * (PowerSeries.coeff n) genocchiPowerSeries

/-- **The Genocchi power series is $2x/(e^x + 1)$.** The Genocchi power series equals
$2x \cdot (e^x + 1)^{-1}$ in $\mathbb{Q}[[x]]$, where $e^x = \sum_{n \ge 0} x^n / n!$ is the
exponential power series and $(e^x + 1)^{-1}$ is the inverse of $e^x + 1$ among formal power
series. -/
public theorem genocchiPowerSeries_eq :
    genocchiPowerSeries = 2 * PowerSeries.X * (PowerSeries.exp ℚ + 1)⁻¹ :=
  rfl

/-- **Genocchi numbers from their generating function.** For every natural number $n$, the
Genocchi number $G_n$ equals $n!$ times the coefficient of $x^n$ in the Genocchi power series
$\frac{2x}{e^x + 1} \in \mathbb{Q}[[x]]$. -/
public theorem genocchiNumber_eq (n : ℕ) :
    genocchiNumber n = (n.factorial : ℚ) * (PowerSeries.coeff n) genocchiPowerSeries :=
  rfl

end

end MetaMathlibExt
