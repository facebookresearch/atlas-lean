/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.ModEq
import MathlibExt.NumberTheory.Recurrences.CRecursiveModularRepresentations

/-!
# Iterated remainders for C-recursive sequences

For a negative residue, the double remainder can be recovered from the Euclidean quotient
when the resulting product is smaller than the outer modulus. For a positive residue, the
corresponding identity uses the negated dividend.
-/

public section

namespace MetaMathlibExt

/--
**Remainder of a remainder, negative residue case.** Let $a$, $A$, $B$ and $C$ be integers with
$A > 0$, $B > 0$ and $C \ge 2$ such that $C$ divides $A$, $B$ does not divide $A$, $a < 0$ and
$B \equiv a \pmod C$. Write $\lfloor A/B \rfloor$ for the floor of $A/B$ and $X \bmod M$ for the
remainder of $X$ modulo $M$ in $\{0, 1, \dots, M - 1\}$. If
$|a| \cdot (\lfloor A/B \rfloor \bmod C) < C$, then
$(A \bmod B) \bmod C = |a| \cdot (\lfloor A/B \rfloor \bmod C)$.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Lemma 7(i).
-/
theorem emod_emod_eq_abs_mul_ediv_emod_of_neg
    (a A B C : ℤ)
    (hA : 0 < A) (hB : 0 < B) (hC : 2 ≤ C)
    (hCA : C ∣ A) (hBA : ¬ B ∣ A)
    (hcongr : B % C = a % C) (ha : a < 0)
    (hbound : |a| * ((A / B) % C) < C) :
    (A % B) % C = |a| * ((A / B) % C) := by
  -- The negative case does not need these hypotheses from the source statement.
  have _ : 0 < A ∧ 0 < B ∧ ¬ B ∣ A := ⟨hA, hB, hBA⟩
  have hC₀ : C ≠ 0 := by omega
  have hA₀ : A ≡ 0 [ZMOD C] := by
    change A % C = 0 % C
    rw [Int.emod_eq_zero_of_dvd hCA, Int.zero_emod]
  have hBa : B ≡ a [ZMOD C] := hcongr
  have hq : A / B ≡ (A / B) % C [ZMOD C] := (Int.mod_modEq _ _).symm
  calc
    (A % B) % C = (A - B * (A / B)) % C := by rw [Int.emod_def A B]
    _ = (|a| * ((A / B) % C)) % C := by
      simpa only [zero_sub, ← Int.neg_mul, abs_of_neg ha] using (hA₀.sub (hBa.mul hq)).eq
    _ = _ := Int.emod_eq_of_lt
      (Int.mul_nonneg (abs_nonneg a) (Int.emod_nonneg (A / B) hC₀)) hbound

/--
**Remainder of a remainder, positive residue case.** Let $a$, $A$, $B$ and $C$ be integers with
$A > 0$, $B > 0$ and $C \ge 2$ such that $C$ divides $A$, $B$ does not divide $A$, $a > 0$ and
$B \equiv a \pmod C$. Write $\lfloor A/B \rfloor$ for the floor of $A/B$ and $X \bmod M$ for the
remainder of $X$ modulo $M$ in $\{0, 1, \dots, M - 1\}$. If
$a + a \cdot (\lfloor A/B \rfloor \bmod C) < C$, then
$((-A) \bmod B) \bmod C = a \cdot \bigl(1 + (\lfloor A/B \rfloor \bmod C)\bigr)$.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Lemma 7(ii).
-/
theorem neg_emod_emod_eq_mul_one_add_ediv_emod_of_pos
    (a A B C : ℤ)
    (hA : 0 < A) (hB : 0 < B) (hC : 2 ≤ C)
    (hCA : C ∣ A) (hBA : ¬ B ∣ A)
    (hcongr : B % C = a % C) (ha : 0 < a)
    (hbound : a + a * ((A / B) % C) < C) :
    ((-A) % B) % C = a * (1 + (A / B) % C) := by
  have hB₁ : B ≠ 1 := by
    rintro rfl
    exact hBA (one_dvd A)
  have hquot := neg_ediv_eq_ediv_add_one_of_not_dvd A B (by omega) (by omega) hBA
  have hBa : B ≡ a [ZMOD C] := hcongr
  have hq : A / B ≡ (A / B) % C [ZMOD C] := (Int.mod_modEq _ _).symm
  calc
    ((-A) % B) % C = (-A + B * (1 + A / B)) % C := by
      rw [Int.emod_def (-A) B, sub_eq_add_neg, ← Int.mul_neg, hquot, add_comm (A / B)]
    _ = (a * (1 + (A / B) % C)) % C := by
      simpa only [neg_zero, zero_add] using
        (hCA.modEq_zero_int.neg.add (hBa.mul (hq.add_left 1))).eq
    _ = _ := by
      apply Int.emod_eq_of_lt
      · have hr := Int.emod_nonneg (A / B) (show C ≠ 0 by omega)
        exact Int.mul_nonneg ha.le (by omega)
      · simpa only [Int.mul_add, Int.mul_one] using hbound

end MetaMathlibExt
