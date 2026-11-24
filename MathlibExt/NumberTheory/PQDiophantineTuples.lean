/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.Coprime.Basic

/-!
# Divisibility in `S`-Diophantine tuples

Lemma 1 of Volker Ziegler, *On the Existence of `{p, q}`-Diophantine
Quadruples and Quintuples*, INTEGERS 25 (2025), Article A92, quoting
Szalay and Ziegler (2013), Lemma 2.1.

If `ac + 1 ∣ bc + 1`, then `ac + 1` divides
`b (ac + 1) - a (bc + 1) = b - a`, which is positive and smaller than
`c ≤ ac`.

For a quadruple, each entry divides the gcd of the three reduced differences
formed from the products involving that entry (`dvd_gcd_sub_div_gcd`).
-/

@[expose] public section

namespace MetaMathlibExt

/-- If `a < b < c` are positive integers, then `ac + 1` does not divide
`bc + 1`. The paper states this for `S`-Diophantine triples; the
`S`-unit hypothesis is not needed.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine
Quadruples and Quintuples*, INTEGERS 25 (2025), Article A92, Lemma 1,
quoting Szalay and Ziegler (2013), Lemma 2.1
(`integers-2025-A92-lem-1`).
Proves `Wanted` entry `not_mul_add_one_dvd_mul_add_one`. -/
theorem not_mul_add_one_dvd_mul_add_one {a b c : ℕ} (ha : 0 < a)
    (hab : a < b) (hbc : b < c) : ¬(a * c + 1 ∣ b * c + 1) := by
  intro h
  have h1 : a * c + 1 ∣ b * (a * c + 1) - a * (b * c + 1) :=
    Nat.dvd_sub (Nat.dvd_mul_left _ _) (Nat.dvd_trans h (Nat.dvd_mul_left _ _))
  have h2 : b * (a * c + 1) - a * (b * c + 1) = b - a := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one,
      Nat.mul_left_comm b a c, ← Nat.mul_assoc a b c]
    omega
  rw [h2] at h1
  have h3 := Nat.le_of_dvd (by omega) h1
  have h4 : c ≤ a * c := Nat.le_mul_of_pos_left c ha
  omega

/-- **$a$, $b$, $c$, $d$ divide gcds of reduced differences.** Let $a, b, c, d$ be natural numbers
and put $s_1 = ab + 1$, $s_2 = ac + 1$, $s_3 = ad + 1$, $s_4 = bc + 1$, $s_5 = bd + 1$,
$s_6 = cd + 1$. For indices $i, j$ let $t_{ij}$ be the integer $(s_j - s_i) / \gcd(s_j, s_i)$.
Then $a \mid \gcd(t_{12}, t_{13}, t_{23})$, $b \mid \gcd(t_{14}, t_{15}, t_{45})$,
$c \mid \gcd(t_{24}, t_{26}, t_{46})$ and $d \mid \gcd(t_{35}, t_{36}, t_{56})$ in $\mathbb{Z}$.

The source assumes that $\{a, b, c, d\}$ is $S$-Diophantine; that hypothesis is not needed.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Lemma 3, quoting Szalay and Ziegler (2013), Lemma 3
(`integers-2025-A92-lem-3`). -/
theorem dvd_gcd_sub_div_gcd (a b c d : ℕ) :
    let s : Fin 6 → ℤ := ![a * b + 1, a * c + 1, a * d + 1, b * c + 1, b * d + 1, c * d + 1]
    let t : Fin 6 → Fin 6 → ℤ := fun i j => (s j - s i) / gcd (s j) (s i)
    (a : ℤ) ∣ gcd (gcd (t 0 1) (t 0 2)) (t 1 2) ∧
      (b : ℤ) ∣ gcd (gcd (t 0 3) (t 0 4)) (t 3 4) ∧
      (c : ℤ) ∣ gcd (gcd (t 1 3) (t 1 5)) (t 3 5) ∧
      (d : ℤ) ∣ gcd (gcd (t 2 4) (t 2 5)) (t 4 5) := by
  have reduced (x y z : ℤ) :
      x ∣ ((x * z + 1) - (x * y + 1)) / gcd (x * z + 1) (x * y + 1) := by
    have coprime : IsCoprime x (gcd (x * z + 1) (x * y + 1)) :=
      (isCoprime_one_right.mul_add_left_right z).of_isCoprime_of_dvd_right (gcd_dvd_left ..)
    apply Int.dvd_ediv_of_mul_dvd
    apply coprime.symm.mul_dvd (Int.dvd_sub (gcd_dvd_left ..) (gcd_dvd_right ..))
    rw [add_sub_add_right_eq_sub, ← mul_sub]
    exact dvd_mul_right ..
  have triple (x y z w : ℤ) :=
    dvd_gcd (dvd_gcd (reduced x y z) (reduced x y w)) (reduced x z w)
  dsimp only [Matrix.cons_val]
  refine ⟨triple a b c d, ?_, ?_, ?_⟩
  · simpa only [mul_comm] using triple b a c d
  · simpa only [mul_comm] using triple c a b d
  · simpa only [mul_comm] using triple d a b c

end MetaMathlibExt
