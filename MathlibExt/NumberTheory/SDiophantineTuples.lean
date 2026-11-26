/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# `S`-Diophantine tuples and the Case IV bound

The Case IV factorizations give two estimates for the ratio `c / b` and hence an upper
bound on `d`. The pure `q`-power `ad + 1` then gives the bound on `b`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **$S$-Diophantine tuples.** Let $S$ be a finite set of natural numbers. A finite set $s$ of
natural numbers is an $S$-Diophantine tuple if all its elements are positive and, for all
distinct $a, b \in s$, every prime factor of $ab + 1$ lies in $S$. A tuple $(a_1, \dots, a_m)$ of
distinct positive integers is encoded by the set of its entries, which has $m$ elements.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Section 1 (definition of `S`-Diophantine `m`-tuples). -/
def IsSDiophantineTuple (S s : Finset ℕ) : Prop :=
  (∀ a ∈ s, 0 < a) ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (a * b + 1).primeFactors ⊆ S

end

private theorem eq_pow_padicValNat_mul_pow_padicValNat {p q n : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (hn : n ≠ 0) (hs : n.primeFactors ⊆ {p, q}) :
    n = p ^ padicValNat p n * q ^ padicValNat q n := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  rw [Nat.padicValNat_def, Nat.padicValNat_def, Nat.multiplicity_eq_factorization hp,
    Nat.multiplicity_eq_factorization hq]
  calc
    n = n.factorization.prod (· ^ ·) := (Nat.prod_factorization_pow_eq_self hn).symm
    _ = ∏ r ∈ ({p, q} : Finset ℕ), r ^ n.factorization r :=
      n.factorization.prod_of_support_subset hs (· ^ ·) (fun _ _ ↦ pow_zero _)
    _ = _ := Finset.prod_pair hpq

-- Only the five products that occur in the ratio and divisibility estimates are needed.
private theorem caseIV_bound_of_products {a b c d G T U : ℕ} (ha : 0 < a) (hbc : b < c)
    (hcd : c < d) (hT : 0 < T) (hs₁ : 35 ≤ a * b + 1) (hs₂ : a * c + 1 = (a * b + 1) * T)
    (hs₃ : 125 ≤ a * d + 1) (hs₅ : b * d + 1 = G * T) (hs₆ : c * d + 1 = G * U) :
    (b : ℝ) < 1042 / 1000 * T := by
  -- Cancel the common divisor G from cd + 1 and bd + 1: it is coprime to their shared d.
  have hUT : T < U := by
    have h : b * d + 1 < c * d + 1 := by
      exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right hbc (by omega)) 1
    rw [hs₅, hs₆] at h
    exact Nat.lt_of_mul_lt_mul_left h
  have hG : G ∣ b * d + 1 := hs₅ ▸ dvd_mul_right G T
  have hcop : d.Coprime G := Nat.Coprime.of_dvd_right hG (by simp)
  have hdvd : d ∣ U - T := by
    apply hcop.dvd_of_dvd_mul_left
    rw [Nat.mul_sub, ← hs₆, ← hs₅, Nat.add_sub_add_right, ← Nat.sub_mul]
    exact dvd_mul_left d (c - b)
  have hdU : d < U := by
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt hUT) hdvd
    omega
  -- Cross-multiply both estimates for c / b, without introducing division.
  have har : 0 < (a : ℝ) := by exact_mod_cast ha
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hbcr : (b : ℝ) < c := by exact_mod_cast hbc
  have h₁ : (35 : ℝ) ≤ (a : ℝ) * b + 1 := by exact_mod_cast hs₁
  have h₂ : (a : ℝ) * c + 1 = ((a : ℝ) * b + 1) * T := by exact_mod_cast hs₂
  have h₅ : (b : ℝ) * d + 1 = (G : ℝ) * T := by exact_mod_cast hs₅
  have h₆ : (c : ℝ) * d + 1 = (G : ℝ) * U := by exact_mod_cast hs₆
  have hlower : (b : ℝ) * U < (c : ℝ) * T := by
    apply lt_of_mul_lt_mul_left ?_ (Nat.cast_nonneg G)
    calc
      _ = (b : ℝ) * ((c : ℝ) * d + 1) := by rw [h₆]; ring
      _ < (c : ℝ) * ((b : ℝ) * d + 1) := by nlinarith only [hbcr]
      _ = _ := by rw [h₅]; ring
  have hupper : (c : ℝ) < 103 / 100 * b * T := by
    have hab' : (1 : ℝ) < 3 / 100 * ((a : ℝ) * b) := by linarith only [h₁]
    apply lt_of_mul_lt_mul_left ?_ har.le
    nlinarith only [h₂, mul_lt_mul_of_pos_right hab' hTr]
  have hU : (U : ℝ) < 103 / 100 * (T : ℝ) ^ 2 := by
    apply lt_of_mul_lt_mul_left ?_ (Nat.cast_nonneg b)
    nlinarith only [hlower, mul_lt_mul_of_pos_right hupper hTr]
  have hd : (d : ℝ) < 103 / 100 * (T : ℝ) ^ 2 :=
    (show (d : ℝ) < (U : ℝ) by exact_mod_cast hdU).trans hU
  -- Since ad + 1 ≥ 125 and ad > ac, we have ad > (124/125) * (ac + 1).
  have h₃ : (125 : ℝ) ≤ (a : ℝ) * d + 1 := by exact_mod_cast hs₃
  have had : (124 / 125 : ℝ) * ((a : ℝ) * d + 1) ≤ (a : ℝ) * d := by
    linarith only [h₃]
  have hcdr : (c : ℝ) < d := by exact_mod_cast hcd
  have hacd : (a : ℝ) * c + 1 < (a : ℝ) * d + 1 :=
    add_lt_add_left (mul_lt_mul_of_pos_left hcdr har) 1
  have hac : (124 / 125 : ℝ) * ((a : ℝ) * c + 1) < (a : ℝ) * d :=
    (mul_lt_mul_of_pos_left hacd (by norm_num)).trans_le had
  have hb : (124 / 125 : ℝ) * b < 103 / 100 * T := by
    rw [h₂] at hac
    apply lt_of_mul_lt_mul_left ?_ (mul_nonneg har.le hTr.le)
    nlinarith only [hac, hTr, mul_lt_mul_of_pos_left hd har]
  linarith only [hb, hTr]

/-- **Bound on $b$ in Case IV for $\{p, q\}$-Diophantine quadruples.** Let $p$ and $q$ be
primes with $p \equiv 3 \pmod 4$, $p \ge 7$ and $q \equiv 1 \pmod 4$, and let $a < b < c < d$
be natural numbers such that $\{a, b, c, d\}$ is a $\{p, q\}$-Diophantine tuple. Write
$s_1, \dots, s_6$ for $ab + 1, ac + 1, ad + 1, bc + 1, bd + 1, cd + 1$, and let $\alpha_i$ and
$\beta_i$ be the exponents of $p$ and $q$ in the prime factorization of $s_i$. Suppose that
$0 = \alpha_3 = \alpha_4 < \alpha_1 = \alpha_2 < \alpha_5 < \alpha_6$ and
$0 < \beta_1 = \beta_6 < \beta_2 = \beta_5$, $\beta_5 < \beta_3$, $\beta_5 < \beta_4$. Then
$b < 1.042 \, q^{\beta_2 - \beta_1}$.

The assumptions on the exponents are Case IV of Table 1 of the source together with
$\beta_1 > 0$.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Lemma 7 (`integers-2025-A92-lem-7`). -/
public theorem sDiophantine_quadruple_caseIV_bound {p q a b c d : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hp3 : p % 4 = 3) (hp7 : 7 ≤ p) (hq1 : q % 4 = 1) (hab : a < b)
    (hbc : b < c) (hcd : c < d) (hS : IsSDiophantineTuple {p, q} {a, b, c, d})
    (hcase : padicValNat p (a * d + 1) = 0 ∧ padicValNat p (b * c + 1) = 0 ∧
      0 < padicValNat p (a * b + 1) ∧ padicValNat p (a * b + 1) = padicValNat p (a * c + 1) ∧
      padicValNat p (a * c + 1) < padicValNat p (b * d + 1) ∧
      padicValNat p (b * d + 1) < padicValNat p (c * d + 1) ∧
      0 < padicValNat q (a * b + 1) ∧ padicValNat q (a * b + 1) = padicValNat q (c * d + 1) ∧
      padicValNat q (c * d + 1) < padicValNat q (a * c + 1) ∧
      padicValNat q (a * c + 1) = padicValNat q (b * d + 1) ∧
      padicValNat q (b * d + 1) < padicValNat q (a * d + 1) ∧
      padicValNat q (b * d + 1) < padicValNat q (b * c + 1)) :
    let β := padicValNat q (a * b + 1)
    let β' := padicValNat q (a * c + 1)
    (b : ℝ) < 1042 / 1000 * (q : ℝ) ^ (β' - β) := by
  dsimp only
  set α := padicValNat p (a * b + 1)
  set α₅ := padicValNat p (b * d + 1)
  set α₆ := padicValNat p (c * d + 1)
  set β := padicValNat q (a * b + 1)
  set β' := padicValNat q (a * c + 1)
  set β₃ := padicValNat q (a * d + 1)
  obtain ⟨hα₃, _, hα, hα₁₂, _, hα₅₆, hβ, hβ₁₆, hβ₆₂, hβ₂₅, hβ₅₃, _⟩ := hcase
  have hpq : p ≠ q := by
    rintro rfl
    omega
  have hq5 : 5 ≤ q := by have := hq.two_le; omega
  have ha : 0 < a := hS.1 a (by simp)
  have hd' : a < d := hab.trans (hbc.trans hcd)
  have factor {x y : ℕ} (hx : x ∈ ({a, b, c, d} : Finset ℕ)) (hy : y ∈ ({a, b, c, d} : Finset ℕ))
      (hxy : x < y) : x * y + 1 = p ^ padicValNat p (x * y + 1) * q ^ padicValNat q (x * y + 1) :=
    eq_pow_padicValNat_mul_pow_padicValNat hp hq hpq (Nat.succ_ne_zero _) (hS.2 x hx y hy hxy.ne)
  let T := q ^ (β' - β)
  let U := p ^ (α₆ - α₅)
  let G := p ^ α₅ * q ^ β
  have hqsplit : q ^ β' = q ^ β * T := by
    dsimp only [T]
    rw [← pow_add, Nat.add_sub_of_le (hβ₁₆.trans_lt hβ₆₂).le]
  have hpsplit : p ^ α₆ = p ^ α₅ * U := by
    dsimp only [U]
    rw [← pow_add, Nat.add_sub_of_le hα₅₆.le]
  have h₁ : a * b + 1 = p ^ α * q ^ β := factor (by simp) (by simp) hab
  have hs₁ : 35 ≤ a * b + 1 := by
    rw [h₁]
    calc
      35 ≤ p ^ 1 * q ^ 1 := by simpa only [pow_one] using Nat.mul_le_mul hp7 hq5
      _ ≤ p ^ α * q ^ β :=
        Nat.mul_le_mul (pow_le_pow_right₀ hp.one_lt.le hα) (pow_le_pow_right₀ hq.one_lt.le hβ)
  have hs₂ : a * c + 1 = (a * b + 1) * T := by
    rw [factor (by simp) (by simp) (hab.trans hbc), ← hα₁₂, hqsplit, h₁, mul_assoc]
  have hs₃ : 125 ≤ a * d + 1 := by
    have heq : a * d + 1 = q ^ β₃ := by
      simpa only [hα₃, pow_zero, one_mul] using factor (by simp) (by simp) hd'
    rw [heq]
    calc
      125 = 5 ^ 3 := by decide
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq5 3
      _ ≤ q ^ β₃ := pow_le_pow_right₀ hq.one_lt.le (by omega)
  have hs₅ : b * d + 1 = G * T := by
    rw [factor (by simp) (by simp) (hbc.trans hcd), ← hβ₂₅, hqsplit]
    exact (mul_assoc _ _ _).symm
  have hs₆ : c * d + 1 = G * U := by
    rw [factor (by simp) (by simp) hcd, ← hβ₁₆, hpsplit]
    exact mul_right_comm _ _ _
  have hT : 0 < T := pow_pos hq.pos _
  simpa only [T, Nat.cast_pow] using caseIV_bound_of_products ha hbc hcd hT hs₁ hs₂ hs₃ hs₅ hs₆

end MetaMathlibExt
