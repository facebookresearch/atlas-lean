/-
Copyright (c) 2026 Alex Kontorovich and contributors, Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich and contributors, Adam Kiezun
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# Completely multiplicative arithmetic functions

This module defines `ArithmeticFunction.IsCompletelyMultiplicative`,
its projection `IsCompletelyMultiplicative.map_mul`, and the
normalization bridge `IsCompletelyMultiplicative.isMultiplicative` to
`ArithmeticFunction.IsMultiplicative`.

References: arXiv:2304.03121v4 `main.tex` lines 237--241
(Furstenberg systems of pretentious and MRT multiplicative functions);
PrimeNumberTheoremAnd at revision `be5e07e04cde20c5ceabf63759bd097a9c88173f`.
-/

@[expose] public section

namespace ArithmeticFunction

variable {R : Type*}

/-- **Completely multiplicative arithmetic function.** Let $R$ be a type with a multiplication and
a zero. An arithmetic function $f$ with values in $R$ (so $f(0) = 0$) is completely multiplicative
if $f(mn) = f(m) f(n)$ for all $m, n \in \mathbb{N} = \{0, 1, 2, \dots\}$.

The normalization $f(1) = 1$ is not part of the definition. -/
def IsCompletelyMultiplicative [Mul R] [Zero R] (f : ArithmeticFunction R) : Prop :=
  ∀ m n : ℕ, f (m * n) = f m * f n

/-- **Completely multiplicative functions preserve products.** Let $R$ be a type with a
multiplication and a zero, and let $f$ be a completely multiplicative arithmetic function with
values in $R$. Then $f(mn) = f(m) f(n)$ for all $m, n \in \mathbb{N}$. -/
@[simp]
theorem IsCompletelyMultiplicative.map_mul [Mul R] [Zero R] {f : ArithmeticFunction R}
    (hf : f.IsCompletelyMultiplicative) (m n : ℕ) : f (m * n) = f m * f n :=
  hf m n

/-- **Normalized completely multiplicative functions are multiplicative.** Let $R$ be a monoid
with zero and let $f$ be a completely multiplicative arithmetic function with values in $R$ such
that $f(1) = 1$. Then $f$ is multiplicative: $f(1) = 1$ and $f(mn) = f(m) f(n)$ for all coprime
natural numbers $m$ and $n$. -/
theorem IsCompletelyMultiplicative.isMultiplicative [MonoidWithZero R]
    {f : ArithmeticFunction R} (hf : f.IsCompletelyMultiplicative) (h1 : f 1 = 1) :
    f.IsMultiplicative :=
  ⟨h1, fun _ => hf _ _⟩

end ArithmeticFunction
