/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Kalman–Mena (a, b)-generalized Fibonacci sequence

Formalizes concept `jis_sem_34b8a222e3026d94d1de5306`
(source statement `jis_34b8a222e3026d94d1de5306`, Perminova, JIS VOL28):
for real parameters `a` and `b`, the sequence with `F 0 = 0`, `F 1 = 1`,
recurrence `F (n + 2) = a * F (n + 1) + b * F n`, and ordinary formal
generating series `x / (1 - a * x - b * x ^ 2)`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Kalman–Mena generalized Fibonacci sequence.** A Kalman–Mena $(a,b)$-generalized
Fibonacci sequence consists of real parameters $a$ and $b$ together with a real sequence
$(F_n)_{n \ge 0}$ such that $F_0 = 0$, $F_1 = 1$, $F_{n+2} = a F_{n+1} + b F_n$ for every
$n \ge 0$, and its ordinary generating series in the formal variable $x$ satisfies the
identity of formal power series $(1 - a x - b x^2) \sum_{n \ge 0} F_n x^n = x$, that is,
$\sum_{n \ge 0} F_n x^n = x / (1 - a x - b x^2)$.

Source: concept `jis_sem_34b8a222e3026d94d1de5306`, source statement
`jis_34b8a222e3026d94d1de5306`. -/
structure AbGeneralizedFibonacciSequence where
  /-- Real parameter `a` (clause `domain`;
  concept `jis_sem_34b8a222e3026d94d1de5306`;
  source statement `jis_34b8a222e3026d94d1de5306`). -/
  a : ℝ
  /-- Real parameter `b` (clause `domain`;
  concept `jis_sem_34b8a222e3026d94d1de5306`;
  source statement `jis_34b8a222e3026d94d1de5306`). -/
  b : ℝ
  /-- The generalized Fibonacci sequence
  (concept `jis_sem_34b8a222e3026d94d1de5306`;
  source statement `jis_34b8a222e3026d94d1de5306`). -/
  F : ℕ → ℝ
  /-- Initial value `F 0 = 0` (clause `initial_zero`;
  concept `jis_sem_34b8a222e3026d94d1de5306`;
  source statement `jis_34b8a222e3026d94d1de5306`). -/
  initial_zero : F 0 = 0
  /-- Initial value `F 1 = 1` (clause `initial_one`;
  concept `jis_sem_34b8a222e3026d94d1de5306`;
  source statement `jis_34b8a222e3026d94d1de5306`). -/
  initial_one : F 1 = 1
  /-- Recurrence `F (n + 2) = a * F (n + 1) + b * F n` (clause `recurrence`;
  concept `jis_sem_34b8a222e3026d94d1de5306`;
  source statement `jis_34b8a222e3026d94d1de5306`). -/
  recurrence : ∀ n : ℕ, F (n + 2) = a * F (n + 1) + b * F n
  /-- Ordinary generating series identity
  `(1 - a * X - b * X ^ 2) * mk F = X`, i.e. `mk F = x / (1 - a * x - b * x ^ 2)`
  (clause `generating_function`;
  concept `jis_sem_34b8a222e3026d94d1de5306`;
  source statement `jis_34b8a222e3026d94d1de5306`). -/
  gen_eq :
    (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.C b * PowerSeries.X ^ 2) *
      PowerSeries.mk F = PowerSeries.X

/-- **Extensionality for Kalman–Mena generalized Fibonacci sequences.** Two Kalman–Mena
$(a,b)$-generalized Fibonacci sequences are equal when they have the same parameter $a$, the same
parameter $b$ and the same sequence $(F_n)_{n \ge 0}$. -/
@[ext]
theorem AbGeneralizedFibonacciSequence.ext
    {x y : AbGeneralizedFibonacciSequence}
    (ha : x.a = y.a) (hb : x.b = y.b) (hF : x.F = y.F) : x = y := by
  cases x
  cases y
  cases ha
  cases hb
  cases hF
  rfl

end

end MetaMathlibExt
