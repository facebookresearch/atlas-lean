/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.EntireExponentialIntegral

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Principal exponential-integral definitions

This module fixes the principal `E1` and asymptotic-remainder normalizations
used by the local DLMF proof. It introduces no assumptions.

The classical principal `E1` has a logarithmic singularity at `z = 0`, so the
standard-named definitions below take an explicit `z ≠ 0` proof argument. The
`Raw`-suffixed helpers are totalized extensions that reuse Lean's junk values
(`Complex.log 0 = 0`, `x / 0 = 0`); they exist so internal differentiability
arguments and the zero-value regressions can be stated, and must not be used
as the classical `E1` at the singular point.
-/

@[expose] public section

namespace Complex

noncomputable section

open scoped BigOperators

/-- **Totalized principal exponential integral.** For every complex number $z$, this is
$\operatorname{Ein}(z) - \operatorname{Log} z - \gamma$, where
$\operatorname{Ein}(z) = \sum_{j \ge 1} (-1)^{j+1} z^j / (j \cdot j!)$ is the entire exponential
integral, $\operatorname{Log}$ is the principal branch of the complex logarithm (imaginary part
in $(-\pi, \pi]$) extended by $\operatorname{Log} 0 = 0$, and $\gamma$ is the Euler–Mascheroni
constant.

At $z = 0$ the value is therefore $-\gamma$. This is a convention, not a value of the classical
principal $E_1$, which has a logarithmic singularity at $0$. -/
def principalExponentialIntegralE1Raw (z : ℂ) : ℂ :=
  ein z - Complex.log z - (Real.eulerMascheroniConstant : ℂ)

/-- **The principal exponential integral.** For a nonzero complex number $z$, the principal
exponential integral is $E_1(z) = \operatorname{Ein}(z) - \operatorname{Log} z - \gamma$, where
$\operatorname{Ein}(z) = \sum_{j \ge 1} (-1)^{j+1} z^j / (j \cdot j!)$ is the entire exponential
integral, $\operatorname{Log}$ is the principal branch of the complex logarithm (imaginary part
in $(-\pi, \pi]$) and $\gamma$ is the Euler–Mascheroni constant.

This is the connection formula DLMF 6.2.4, taken as the definition. On the branch cut, the
negative real axis, the value is the one given by the principal logarithm. -/
def principalExponentialIntegralE1 (z : ℂ) (_hz : z ≠ 0) : ℂ :=
  principalExponentialIntegralE1Raw z

/-- **Totalized asymptotic term of $E_1$.** For $n \in \mathbb{N}$ and every complex number $z$,
the $n$-th term of the asymptotic expansion of $E_1$ is
$\frac{e^{-z}}{z} \cdot \frac{(-1)^n \, n!}{z^n}$, with division by zero read as $0$.

At $z = 0$ this gives $0$, a value with no classical meaning; the domain-safe term requires
$z \neq 0$. -/
def e1AsymptoticTermRaw (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-z) / z *
    ((-1 : ℂ) ^ n * (n.factorial : ℂ) / z ^ n)

/-- **Asymptotic term of $E_1$.** For $n \in \mathbb{N}$ and a nonzero complex number $z$, the
$n$-th term of the asymptotic expansion of the exponential integral $E_1$ is
$\frac{e^{-z}}{z} \cdot \frac{(-1)^n \, n!}{z^n}$. -/
def e1AsymptoticTerm (n : ℕ) (z : ℂ) (_hz : z ≠ 0) : ℂ :=
  e1AsymptoticTermRaw n z

/-- **Totalized partial sum of the $E_1$ asymptotic expansion.** For $n \in \mathbb{N}$ and every
complex number $z$, this is $\sum_{j < n} t_j(z)$, where
$t_j(z) = \frac{e^{-z}}{z} \cdot \frac{(-1)^j \, j!}{z^j}$ with division by zero read as $0$.

At $z = 0$ every term, hence the sum, is $0$; this value has no classical meaning, and the
domain-safe partial sum requires $z \neq 0$. -/
def e1AsymptoticPartialRaw (n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range n, e1AsymptoticTermRaw j z

/-- **Partial sum of the $E_1$ asymptotic expansion.** For $n \in \mathbb{N}$ and a nonzero complex
number $z$, the sum of the first $n$ terms of the asymptotic expansion of the exponential
integral $E_1$ is $\sum_{j < n} \frac{e^{-z}}{z} \cdot \frac{(-1)^j \, j!}{z^j}$. -/
def e1AsymptoticPartial (n : ℕ) (z : ℂ) (hz : z ≠ 0) : ℂ :=
  ∑ j ∈ Finset.range n, e1AsymptoticTerm j z hz

/-- **Totalized remainder of the $E_1$ asymptotic expansion.** For $n \in \mathbb{N}$ and every
complex number $z$, this is $\operatorname{Ein}(z) - \operatorname{Log} z - \gamma - S_n(z)$,
where $\operatorname{Ein}$ is the entire exponential integral, $\operatorname{Log}$ is the
principal logarithm extended by $\operatorname{Log} 0 = 0$, $\gamma$ is the Euler–Mascheroni
constant and $S_n$ is the totalized sum of the first $n$ terms of the asymptotic expansion
of $E_1$.

At $z = 0$ this equals $-\gamma$, a value with no classical meaning; the domain-safe remainder
requires $z \neq 0$. -/
def e1AsymptoticRemainderRaw (n : ℕ) (z : ℂ) : ℂ :=
  principalExponentialIntegralE1Raw z - e1AsymptoticPartialRaw n z

/-- **Remainder of the $E_1$ asymptotic expansion.** For $n \in \mathbb{N}$ and a nonzero complex
number $z$, the remainder after $n$ terms is
$E_1(z) - \sum_{j < n} \frac{e^{-z}}{z} \cdot \frac{(-1)^j \, j!}{z^j}$, where $E_1$ is the
principal exponential integral. -/
def e1AsymptoticRemainder (n : ℕ) (z : ℂ) (hz : z ≠ 0) : ℂ :=
  principalExponentialIntegralE1 z hz - e1AsymptoticPartial n z hz

@[simp] theorem principalExponentialIntegralE1_eq_raw (z : ℂ) (hz : z ≠ 0) :
    principalExponentialIntegralE1 z hz = principalExponentialIntegralE1Raw z :=
  rfl

@[simp] theorem e1AsymptoticTerm_eq_raw (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    e1AsymptoticTerm n z hz = e1AsymptoticTermRaw n z :=
  rfl

@[simp] theorem e1AsymptoticPartial_eq_raw (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    e1AsymptoticPartial n z hz = e1AsymptoticPartialRaw n z := by
  simp only [e1AsymptoticPartial, e1AsymptoticPartialRaw, e1AsymptoticTerm_eq_raw]

@[simp] theorem e1AsymptoticRemainder_eq_raw (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    e1AsymptoticRemainder n z hz = e1AsymptoticRemainderRaw n z := by
  simp only [e1AsymptoticRemainder, e1AsymptoticRemainderRaw,
    principalExponentialIntegralE1_eq_raw, e1AsymptoticPartial_eq_raw]

/-- **Totalized principal $E_1$ kernel at zero.** The totalized kernel
$\operatorname{Ein}(z) - \operatorname{Log} z - \gamma$, where $\operatorname{Ein}$ is the entire
exponential integral, $\operatorname{Log}$ is the principal logarithm extended by
$\operatorname{Log} 0 = 0$ and $\gamma$ is the Euler–Mascheroni constant, equals $-\gamma$ at
$z = 0$.

This value comes from $\operatorname{Ein}(0) = 0$ and the convention $\operatorname{Log} 0 = 0$,
not from analysis; the classical $E_1$ is singular at $0$. -/
theorem principalExponentialIntegralE1Raw_zero :
    principalExponentialIntegralE1Raw 0 = -(Real.eulerMascheroniConstant : ℂ) := by
  have hein : ein (0 : ℂ) = 0 := by simp [ein, einTerm]
  simp [principalExponentialIntegralE1Raw, hein, Complex.log_zero]

/-- **Totalized $E_1$ asymptotic terms vanish at zero.** For every $n \in \mathbb{N}$, the
totalized $n$-th term $\frac{e^{-z}}{z} \cdot \frac{(-1)^n \, n!}{z^n}$ of the asymptotic
expansion of $E_1$, with division by zero read as $0$, equals $0$ at $z = 0$.

This value comes from the convention that division by zero gives $0$, not from analysis. -/
theorem e1AsymptoticTermRaw_zero (n : ℕ) :
    e1AsymptoticTermRaw n 0 = 0 := by
  simp [e1AsymptoticTermRaw]

/-- **Totalized partial sums of the $E_1$ expansion vanish at zero.** For every
$n \in \mathbb{N}$, the totalized sum of the first $n$ terms of the asymptotic expansion of $E_1$
equals $0$ at $z = 0$.

This value comes from the convention that division by zero gives $0$, not from analysis. -/
theorem e1AsymptoticPartialRaw_zero (n : ℕ) :
    e1AsymptoticPartialRaw n 0 = 0 := by
  simp [e1AsymptoticPartialRaw, e1AsymptoticTermRaw_zero]

/-- **Totalized $E_1$ remainder at zero.** For every $n \in \mathbb{N}$, the totalized remainder
of the asymptotic expansion of $E_1$ after $n$ terms equals $-\gamma$ at $z = 0$, where $\gamma$
is the Euler–Mascheroni constant.

This value comes from the conventions $\operatorname{Log} 0 = 0$ and division by zero giving
$0$, not from analysis; the classical $E_1$ is singular at $0$. -/
theorem e1AsymptoticRemainderRaw_zero (n : ℕ) :
    e1AsymptoticRemainderRaw n 0 = -(Real.eulerMascheroniConstant : ℂ) := by
  simp [e1AsymptoticRemainderRaw, principalExponentialIntegralE1Raw_zero,
    e1AsymptoticPartialRaw_zero]

end

end Complex
