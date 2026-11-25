/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Data.Nat.Digits.Reverse
import Mathlib.Data.List.Induction
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring

/-!
# Decimal reverse divisors with at most seven digits

Fix the quotient and fill in the digits of the number from both ends. At each step
the outer digits give upper and lower bounds for the number and its reversal, as
well as their residues modulo the current place value.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

/-- **Reverse divisor.** A natural number $n$ is a reverse divisor if $n > 0$ and there is a
natural number $k \ge 2$ such that the decimal reversal of $n$ equals $kn$. Since $n > 0$, such a
$k$ is unique; it is called the quotient of $n$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Section 1 (terminology). -/
def IsReverseDivisor (n : ℕ) : Prop :=
  0 < n ∧ ∃ k : ℕ, 2 ≤ k ∧ Nat.reverseDigits 10 n = k * n

/-- **Characterization of reverse divisors.** A natural number $n$ is a reverse divisor if and
only if $n > 0$ and there is a natural number $k \ge 2$ such that the decimal reversal of $n$
equals $kn$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Section 1 (terminology). -/
theorem isReverseDivisor_iff (n : ℕ) :
    IsReverseDivisor n ↔
      0 < n ∧ ∃ k : ℕ, 2 ≤ k ∧ Nat.reverseDigits 10 n = k * n :=
  Iff.rfl

/-- With `len` digits still to place, write the number as `a + p * m` and its reversal
as `b + p * r`, where `m` and `r` are the two readings of the remaining digits.
Discard a branch if the possible ranges or the residues modulo `p` are incompatible. -/
private def candidates (k : ℕ) : (len p a b : ℕ) → List ℕ
  | 0, _, a, b => if k * a = b then [a] else []
  | 1, p, a, b => (List.range 10).filterMap fun d =>
      if k * (a + p * d) = b + p * d then some (a + p * d) else none
  | len + 2, p, a, b =>
      if k * a % p = b % p ∧ k * a < b + p * 10 ^ (len + 2) ∧
          b < k * (a + p * 10 ^ (len + 2)) then
        (List.range 10).flatMap fun u => (List.range 10).flatMap fun v =>
          candidates k len (10 * p)
            (a + p * (u + 10 ^ (len + 1) * v))
            (b + p * (v + 10 ^ (len + 1) * u))
      else []

private theorem mem_candidates (digits : List ℕ) (hd : ∀ d ∈ digits, d < 10)
    (k p a b : ℕ) (hk : 0 < k) (hp : 0 < p)
    (heq : k * (a + p * Nat.ofDigits 10 digits) = b + p * Nat.ofDigits 10 digits.reverse) :
    a + p * Nat.ofDigits 10 digits ∈ candidates k digits.length p a b := by
  induction digits using List.bidirectionalRec generalizing p a b with
  | nil =>
    simp [candidates, show k * a = b by simpa using heq]
  | singleton d =>
    simp only [List.reverse_singleton, Nat.ofDigits_singleton] at heq
    simp only [Nat.ofDigits_singleton, List.length_singleton, candidates, List.mem_filterMap]
    exact ⟨d, List.mem_range.mpr (hd d (by simp)), by simp [heq]⟩
  | cons_append u ds v ih =>
    let digits := u :: (ds ++ [v])
    have hv : v < 10 := hd v (by simp)
    have hu : u < 10 := hd u (by simp)
    have hds : ∀ d ∈ ds, d < 10 := fun d h => hd d (by simp [h])
    have hlen : digits.length = ds.length + 2 := by simp [digits, Nat.add_assoc]
    have hbound := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 10) hd
    have hrbound := Nat.ofDigits_lt_base_pow_length (l := digits.reverse) (by decide : 1 < 10)
      (fun d h => hd d (List.mem_reverse.mp h))
    change Nat.ofDigits 10 digits < 10 ^ digits.length at hbound
    rw [List.length_reverse] at hrbound
    have hlow : k * a % p = b % p := by
      simpa [Nat.mul_add, Nat.mul_left_comm k p] using congrArg (· % p) heq
    have hupper : k * a < b + p * 10 ^ digits.length := calc
      k * a ≤ k * (a + p * Nat.ofDigits 10 digits) := Nat.mul_le_mul_left k (Nat.le_add_right _ _)
      _ = b + p * Nat.ofDigits 10 digits.reverse := heq
      _ < _ := by gcongr
    have hlower : b < k * (a + p * 10 ^ digits.length) := calc
      b ≤ b + p * Nat.ofDigits 10 digits.reverse := Nat.le_add_right _ _
      _ = k * (a + p * Nat.ofDigits 10 digits) := heq.symm
      _ < _ := by gcongr
    rw [hlen] at hupper hlower
    change a + p * Nat.ofDigits 10 digits ∈ candidates k digits.length p a b
    rw [hlen, candidates, ite_eq_left ⟨hlow, hupper, hlower⟩]
    refine List.mem_flatMap.mpr ⟨u, List.mem_range.mpr hu, List.mem_flatMap.mpr
      ⟨v, List.mem_range.mpr hv, ?_⟩⟩
    have expand (x y z : ℕ) (l : List ℕ) :
        z + p * Nat.ofDigits 10 (x :: (l ++ [y])) =
          z + p * (x + 10 ^ (l.length + 1) * y) + 10 * p * Nat.ofDigits 10 l := by
      rw [Nat.ofDigits_cons, Nat.ofDigits_append, Nat.ofDigits_singleton, pow_succ]
      ring
    rw [show digits = u :: (ds ++ [v]) from rfl, expand]
    apply ih hds _ _ _ (by omega)
    have hr : (u :: (ds ++ [v])).reverse = v :: (ds.reverse ++ [u]) := by simp
    simpa only [hr, expand, List.length_reverse] using heq

/-- **Reverse divisors with at most seven digits.** Let $n$ be a reverse divisor with $L$
decimal digits, where $L \le 7$. Then $n = 11(10^{L-2} - 1)$ or $n = 22(10^{L-2} - 1)$, where
$L - 2$ is read as $0$ when $L < 2$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Theorem 1 (quoted from the literature). -/
theorem eq_basic_of_length_le_seven (n : ℕ)
    (h : IsReverseDivisor n)
    (h7 : (Nat.digits 10 n).length ≤ 7) :
    n = 11 * (10 ^ ((Nat.digits 10 n).length - 2) - 1) ∨
      n = 22 * (10 ^ ((Nat.digits 10 n).length - 2) - 1) := by
  obtain ⟨hn, k, hk, hrev⟩ := h
  have hd : ∀ d ∈ Nat.digits 10 n, d < 10 := fun _ => Nat.digits_lt_base (by decide)
  have hrevlt := Nat.ofDigits_lt_base_pow_length (l := (Nat.digits 10 n).reverse)
    (by decide : 1 < 10) (fun d h => hd d (List.mem_reverse.mp h))
  rw [List.length_reverse] at hrevlt
  have hleading := Nat.base_pow_length_digits_le 10 n (by decide) hn.ne'
  have hk10 : k < 10 := by
    change Nat.reverseDigits 10 n < _ at hrevlt
    rw [hrev] at hrevlt
    exact Nat.lt_of_mul_lt_mul_right (hrevlt.trans_le hleading)
  have hmem := mem_candidates (Nat.digits 10 n) hd k 1 0 0 (by omega) (by decide)
    (by simpa [Nat.reverseDigits, Nat.ofDigits_digits] using hrev.symm)
  simp only [Nat.ofDigits_digits, one_mul, zero_add] at hmem
  have classify : ∀ (l : Fin 8) (q : Fin 10), 2 ≤ q.val →
      ∀ m ∈ candidates q.val l.val 1 0 0, 10 ^ l.val ≤ 10 * m →
        m = 11 * (10 ^ (l.val - 2) - 1) ∨ m = 22 * (10 ^ (l.val - 2) - 1) := by
    decide +kernel
  exact classify ⟨_, by omega⟩ ⟨k, hk10⟩ hk n hmem hleading

/-- **Property $P^*$.** A natural number $n$ has property $P^*$ if $n$ divides the decimal
reversal of every multiple of $n$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Section 2 (terminology). -/
def HasPropertyPStar (n : ℕ) : Prop :=
  ∀ m : ℕ, n ∣ m → n ∣ Nat.reverseDigits 10 m

/-- **Unfolding property $P^*$.** A natural number $n$ has property $P^*$ if and only if $n$
divides the decimal reversal of every multiple of $n$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Section 2 (terminology). -/
theorem hasPropertyPStar_iff (n : ℕ) :
    HasPropertyPStar n ↔
      ∀ m : ℕ, n ∣ m → n ∣ Nat.reverseDigits 10 m :=
  Iff.rfl

/-- **A product congruent to $11$ modulo a power of ten.** For every natural number $r$, let
$a = (10^r - 1) \cdot 100 + 89$, the integer whose decimal digits are $r$ nines followed by $89$,
and let $b = 10^{r+2} - 1$, the integer whose decimal digits are $r + 2$ nines. Then the
remainder of $ab$ modulo $10^{r+2}$ is $11$; that is, the last $r + 2$ decimal digits of $ab$ are
$r$ zeros followed by $11$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Lemma 4. -/
theorem mul_nines_modEq_eleven (r : ℕ) :
    ((10 ^ r - 1) * 100 + 89) * (10 ^ (r + 2) - 1) %
        10 ^ (r + 2) = 11 := by
  have hM : (100 : ℕ) ≤ 10 ^ (r + 2) := by
    calc (100 : ℕ) = 10 ^ 2 := by norm_num
    _ ≤ 10 ^ (r + 2) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA : ((10 ^ r - 1) * 100 + 89 : ℕ) + 11 = 10 ^ (r + 2) := by
    have h1 : 1 ≤ 10 ^ r := Nat.one_le_pow r 10 (by norm_num)
    have h2 : (10 ^ r - 1) * 100 = 10 ^ r * 100 - 100 := by
      rw [Nat.sub_mul, Nat.one_mul]
    rw [h2, pow_add]
    omega
  have hB : (10 ^ (r + 2) - 1 : ℕ) + 1 = 10 ^ (r + 2) :=
    Nat.sub_add_cancel (Nat.one_le_pow _ 10 (by norm_num))
  have hprod : ((10 ^ r - 1) * 100 + 89) * (10 ^ (r + 2) - 1) +
        11 * 10 ^ (r + 2) =
      10 ^ (r + 2) * (10 ^ (r + 2) - 1) + 11 := by
    calc ((10 ^ r - 1) * 100 + 89) * (10 ^ (r + 2) - 1) +
          11 * 10 ^ (r + 2)
        = ((10 ^ r - 1) * 100 + 89) * (10 ^ (r + 2) - 1) +
            11 * ((10 ^ (r + 2) - 1) + 1) := by rw [hB]
    _ = (((10 ^ r - 1) * 100 + 89) + 11) * (10 ^ (r + 2) - 1) + 11 := by
          ring
    _ = 10 ^ (r + 2) * (10 ^ (r + 2) - 1) + 11 := by rw [hA]
  have hmod := congrArg (· % 10 ^ (r + 2)) hprod
  rw [mul_comm 11 (10 ^ (r + 2)), Nat.add_mul_mod_self_left] at hmod
  rw [Nat.add_comm (10 ^ (r + 2) * (10 ^ (r + 2) - 1)) 11,
    Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by omega : 11 < 10 ^ (r + 2))] at hmod
  exact hmod

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted
