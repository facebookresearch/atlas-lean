/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

open scoped BigOperators

@[expose] public section

namespace MetaMathlibExt

/-- **Mahler substitution.** For a formal power series $F \in \mathbb{C}[[z]]$ and natural numbers
$k$ and $i$, let $m = k^i$; the power series $F(z^{k^i})$ is defined coefficientwise. When
$m \ge 1$, its coefficient of $z^n$ is the coefficient of $z^{n/m}$ in $F$ if $m$ divides $n$, and
$0$ otherwise; this is the substitution $z \mapsto z^m$ in $F$. When $m = 0$ (that is, $k = 0$ and
$i \ge 1$), it is the constant series equal to the constant term of $F$.

Source: https://cs.uwaterloo.ca/journals/JIS/VOL16/Bell/bell2.tex (concept
`jis_sem_5181d154d12c87e1c5d03365`, defining statement `jis_e5b3733b8ba6a96c630ed094`). -/
public noncomputable def mahlerSubst
    (F : PowerSeries Complex) (k i : ℕ) : PowerSeries Complex :=
  PowerSeries.mk fun n =>
    if (k ^ i) ∣ n then PowerSeries.coeff (n / (k ^ i)) F else 0

/-- **$k$-Mahler functions.** Let $k$ be a natural number. A formal power series
$F \in \mathbb{C}[[z]]$ is a $k$-Mahler function when $k \ge 2$ and there exist a natural number
$d$ and polynomials $a_0(z), \dots, a_d(z) \in \mathbb{C}[z]$ with $a_0 \ne 0$ and $a_d \ne 0$
such that the following identity holds in $\mathbb{C}[[z]]$:

$$\sum_{i=0}^{d} a_i(z)\, F\bigl(z^{k^i}\bigr) = 0.$$

Source: https://cs.uwaterloo.ca/journals/JIS/VOL16/Bell/bell2.tex (concept
`jis_sem_5181d154d12c87e1c5d03365`, required clause from statement
`jis_e5b3733b8ba6a96c630ed094`). -/
public noncomputable def IsKMahlerFunction (k : ℕ) (F : PowerSeries Complex) : Prop :=
  2 ≤ k ∧
    ∃ (d : ℕ) (a : Fin (d + 1) → Polynomial Complex),
      a ⟨0, Nat.zero_lt_succ d⟩ ≠ 0 ∧
        a ⟨d, Nat.lt_succ_self d⟩ ≠ 0 ∧
          ∑ i : Fin (d + 1),
              Polynomial.toPowerSeries (a i) * mahlerSubst F k i.val = 0

end MetaMathlibExt

end
