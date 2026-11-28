/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.InitialRepetitionsC3

/-!
# Parity of $c_3$ in three progressions modulo eleven

For every natural number $n$, the partition counts $c_3(11n+5)$, $c_3(11n+7)$ and $c_3(11n+9)$
are even. This is the case $p=11$ of the prime-progression parity theorem: for $r=5,7,9$, neither
$12r+1$ nor $8r+1$ is a square modulo $11$.

## References

* John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
  Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
  pp. 1–12, Theorems 6 and 7. <https://math.colgate.edu/~integers/z32/z32.pdf>
* Darlison Nyirenda and Beaullah Mugwangwavari, *Modulo 2 congruences for partitions with
  initial repetitions*, Boletín de la Sociedad Matemática Mexicana (3) 29, no. 3 (2023),
  Article 72, Theorem 4. <https://doi.org/10.1007/s40590-023-00538-8>
-/

namespace MetaMathlibExt

/-- **Parity of $c_3(11n + 5)$, $c_3(11n + 7)$ and $c_3(11n + 9)$.** Let $c_3(m)$ be the number
of partitions of $m$ for which there is an integer $j$ with $1 \le j \le m$ such that the part $1$
appears exactly $j^2$ or $j^2 + 1$ times, the odd parts greater than $1$ are distinct, the even
parts are distinct, and every even part greater than $2j$ is divisible by $4$ and at least
$4j + 4$. Nyirenda and Mugwangwavari: for every integer $n \ge 0$, the numbers $c_3(11n + 5)$,
$c_3(11n + 7)$ and $c_3(11n + 9)$ are all even.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 6 (`integers-2025-A32-thm-6`). -/
public theorem initialRepetitionsC3_eleven_mul_add_even (n : ℕ) :
    Even (initialRepetitionsC3 (11 * n + 5)) ∧ Even (initialRepetitionsC3 (11 * n + 7)) ∧
      Even (initialRepetitionsC3 (11 * n + 9)) := by
  -- Each nonsquare condition is checked by enumerating the possible roots in `ZMod 11`.
  refine ⟨?_, ?_, ?_⟩ <;>
    exact initialRepetitionsC3_prime_mul_add_even 11 _ n (by decide) (by decide) (by decide)
      (by unfold IsSquare; decide) (by unfold IsSquare; decide)

end MetaMathlibExt
