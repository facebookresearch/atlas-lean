/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Cyclic numbers and Oppermann interval counts

These definitions support Joel E. Cohen, *Conjectures about Primes and
Cyclic Numbers*, Journal of Integer Sequences 28 (2025), Article 25.4.1.
-/

namespace MetaMathlibExt

@[expose]
public section

/-- **Cyclic numbers.** A positive integer $n$ is cyclic when $\gcd(n, \varphi(n)) = 1$, where
$\varphi$ is Euler's totient function. -/
def IsCyclicNumber (n : ℕ) : Prop :=
  0 < n ∧ n.Coprime n.totient

/-- **Cyclic numbers in the left Oppermann interval.** For a natural number $n$, this is the
number of cyclic numbers $k$ with $n^2 - n \le k \le n^2$. -/
def oppermannCyclicCountLeft (n : ℕ) : ℕ :=
  letI : DecidablePred IsCyclicNumber := fun k => by
    unfold IsCyclicNumber
    infer_instance
  ((Finset.Icc (n ^ 2 - n) (n ^ 2)).filter IsCyclicNumber).card

/-- **Cyclic numbers in the right Oppermann interval.** For a natural number $n$, this is the
number of cyclic numbers $k$ with $n^2 \le k \le n^2 + n$. -/
def oppermannCyclicCountRight (n : ℕ) : ℕ :=
  letI : DecidablePred IsCyclicNumber := fun k => by
    unfold IsCyclicNumber
    infer_instance
  ((Finset.Icc (n ^ 2) (n ^ 2 + n)).filter IsCyclicNumber).card

/-- **Left-hand approximation for cyclic numbers near squares.** Let $\gamma$ be the
Euler–Mascheroni constant and, for real $x$, let $L(x) = \log \log \log (x^2)$. The left-hand
approximation is the function of the real variable $x$ given by
$$
\frac{x}{e^{\gamma} L(x)} \left(1 - \frac{\gamma}{L(x)}\right).
$$

Here $\log y$ means $\log |y|$, with $\log 0 = 0$, and a quotient by $0$ is $0$, so the expression
is defined for every real $x$. J. E. Cohen conjectures that, at $x = n$, it is asymptotic to
the number of cyclic numbers in $[n^2 - n, n^2]$. -/
noncomputable def oppermannCyclicLeftApproximation (x : ℝ) : ℝ :=
  x / (Real.exp Real.eulerMascheroniConstant *
    Real.log (Real.log (Real.log (x ^ 2)))) *
    (1 - Real.eulerMascheroniConstant /
      Real.log (Real.log (Real.log (x ^ 2))))

/-- **Simplified approximation for cyclic numbers near squares.** Let $\gamma$ be the
Euler–Mascheroni constant and, for real $x$, let $L(x) = \log \log \log x$. The simplified
approximation is the function of the real variable $x$ given by
$$
\frac{x}{e^{\gamma} L(x)} \left(1 - \frac{\gamma}{L(x)}\right).
$$

Here $\log y$ means $\log |y|$, with $\log 0 = 0$, and a quotient by $0$ is $0$, so the expression
is defined for every real $x$. J. E. Cohen conjectures that, at $x = n$, it is asymptotic to
the number of cyclic numbers in $[n^2 - n, n^2]$ and to the number in $[n^2, n^2 + n]$. -/
noncomputable def oppermannCyclicApproximation (x : ℝ) : ℝ :=
  x / (Real.exp Real.eulerMascheroniConstant *
    Real.log (Real.log (Real.log x))) *
    (1 - Real.eulerMascheroniConstant /
      Real.log (Real.log (Real.log x)))

/-- **Right-hand approximation for cyclic numbers near squares.** Let $\gamma$ be the
Euler–Mascheroni constant and, for real $x$, let $L(x) = \log \log \log (x(x+1))$. The right-hand
approximation is the function of the real variable $x$ given by
$$
\frac{x}{e^{\gamma} L(x)} \left(1 - \frac{\gamma}{L(x)}\right).
$$

Here $\log y$ means $\log |y|$, with $\log 0 = 0$, and a quotient by $0$ is $0$, so the expression
is defined for every real $x$. J. E. Cohen conjectures that, at $x = n$, it is asymptotic to
the number of cyclic numbers in $[n^2, n^2 + n]$. -/
noncomputable def oppermannCyclicRightApproximation (x : ℝ) : ℝ :=
  x / (Real.exp Real.eulerMascheroniConstant *
    Real.log (Real.log (Real.log (x * (x + 1))))) *
    (1 - Real.eulerMascheroniConstant /
      Real.log (Real.log (Real.log (x * (x + 1)))))

end

end MetaMathlibExt
