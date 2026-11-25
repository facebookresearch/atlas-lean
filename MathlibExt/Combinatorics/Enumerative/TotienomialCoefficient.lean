/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient

/-!
Verified Edgar-Spivey JIS source:
https://cs.uwaterloo.ca/journals/JIS/VOL19/Edgar/edgar3.tex

Generalized f-factorial and f-binomial coefficient, plus the
totienomial specialization to Euler's phi function.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Generalized factorial.** For a sequence $f \colon \mathbb{N} \to \mathbb{N}$ and a natural
number $n$, the generalized factorial of $f$ at $n$ is the product $f(1) f(2) \cdots f(n)$ of
the values $f(i)$ for $1 \le i \le n$; for $n = 0$ it is the empty product $1$.

Source: https://cs.uwaterloo.ca/journals/JIS/VOL19/Edgar/edgar3.tex -/
def generalizedFactorial (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Finset.prod (Finset.Icc 1 n) f

/-- **Positive sequence.** A sequence $f \colon \mathbb{N} \to \mathbb{N}$ is positive when
$f(i) > 0$ for every $i > 0$; the value $f(0)$ is unrestricted.

This is the condition on $f$ under which the source defines generalized binomial coefficients. -/
def IsPositiveSequence (f : ℕ → ℕ) : Prop :=
  ∀ i, 0 < i → 0 < f i

/-- **Generalized factorials of positive sequences are positive.** Let $f \colon \mathbb{N} \to
\mathbb{N}$ be a positive sequence, that is $f(i) > 0$ for every $i > 0$. Then for every natural
number $n$, the generalized factorial $f(1) f(2) \cdots f(n)$ is positive. -/
theorem generalizedFactorial_pos {f : ℕ → ℕ} (hf : IsPositiveSequence f) (n : ℕ) :
    0 < generalizedFactorial f n := by
  apply Finset.prod_pos
  intro i hi
  exact hf i (Finset.mem_Icc.mp hi).1

/-- **Generalized binomial coefficient.** Let $f \colon \mathbb{N} \to \mathbb{N}$ be a sequence and
write $k!_f = f(1) f(2) \cdots f(k)$ for its generalized factorial, so that $0!_f = 1$. For
natural numbers $n$ and $m$, the generalized binomial coefficient of $f$ is the rational number
$$\binom{n+m}{n}_f = \frac{(n+m)!_f}{n!_f \, m!_f},$$
which is taken to be $0$ when the denominator is $0$.

When $f(i) > 0$ for every $i > 0$, the setting of the source, the denominator is never $0$ and
this is the source's quotient.

Source: https://cs.uwaterloo.ca/journals/JIS/VOL19/Edgar/edgar3.tex -/
def generalizedBinomialCoefficient (f : ℕ → ℕ) (n m : ℕ) : ℚ :=
  (generalizedFactorial f (n + m) : ℚ) /
    ((generalizedFactorial f n : ℚ) * (generalizedFactorial f m : ℚ))

/-- **Defining equation of the generalized binomial coefficient.** Let $f \colon \mathbb{N} \to
\mathbb{N}$ be a positive sequence, that is $f(i) > 0$ for every $i > 0$, and write
$k!_f = f(1) f(2) \cdots f(k)$ for its generalized factorial. Then for all natural numbers $n$
and $m$, the generalized binomial coefficient $\binom{n+m}{n}_f$, defined as
$(n+m)!_f / (n!_f \, m!_f)$ with division by $0$ giving $0$, satisfies
$\binom{n+m}{n}_f \cdot n!_f \, m!_f = (n+m)!_f$ in $\mathbb{Q}$. -/
theorem generalizedBinomialCoefficient_mul_denominator {f : ℕ → ℕ}
    (hf : IsPositiveSequence f) (n m : ℕ) :
    generalizedBinomialCoefficient f n m *
        ((generalizedFactorial f n : ℚ) * (generalizedFactorial f m : ℚ)) =
      generalizedFactorial f (n + m) := by
  apply div_mul_cancel₀
  exact mul_ne_zero
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (generalizedFactorial_pos hf n)))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (generalizedFactorial_pos hf m)))

/-- **Totienomial coefficient.** Let $\varphi$ be Euler's totient function and write
$k!_\varphi = \varphi(1) \varphi(2) \cdots \varphi(k)$. For natural numbers $n$ and $m$, the
totienomial coefficient is the generalized binomial coefficient of $\varphi$, that is the
rational number
$$\binom{n+m}{n}_\varphi = \frac{(n+m)!_\varphi}{n!_\varphi \, m!_\varphi}.$$

Since $\varphi(i) > 0$ for every $i > 0$, the denominator is never $0$.

Source: https://cs.uwaterloo.ca/journals/JIS/VOL19/Edgar/edgar3.tex -/
def totienomialCoefficient (n m : ℕ) : ℚ :=
  generalizedBinomialCoefficient Nat.totient n m

end


end MetaMathlibExt
