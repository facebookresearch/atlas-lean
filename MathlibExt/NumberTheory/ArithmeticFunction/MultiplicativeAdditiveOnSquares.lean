/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination

/-!
# Multiplicative functions additive on pairs of squares

We determine the values on squares from the value at four and deduce the power law
for all even exponents.
-/

namespace MetaMathlibExt

namespace multiplicative_additive_on_squares

/-- The values on odd and even squares are quadratic polynomials in the half-index. -/
private theorem square_values (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ m n : ℕ, 0 < m → 0 < n → f (m ^ 2 + n ^ 2) = f (m ^ 2) + f (n ^ 2)) :
    (∀ n : ℕ, f ((2 * n + 1) ^ 2) = 1 + f 4 * n * (n + 1)) ∧
      (∀ n : ℕ, f ((2 * n) ^ 2) = f 4 * n ^ 2) := by
  let g (n : ℕ) := f (n ^ 2)
  have h1 : g 1 = 1 := by simpa [g] using hf.map_one
  have h2 : f 2 = 2 := by
    simpa [hf.map_one, one_add_one_eq_two] using hadd 1 1 (by decide) (by decide)
  -- The two sums of squares differ by a factor of two, coprime to the smaller sum.
  have shift (n b : ℕ) (hb : 0 < b) :
      g (2 * n + 1 + 2 * b) + g (2 * n + 1) = 2 * (g (2 * n + 1 + b) + g b) := by
    have hcop : Nat.Coprime 2 ((2 * n + 1 + b) ^ 2 + b ^ 2) := by
      apply Nat.coprime_two_left.mpr
      exact ⟨2 * n ^ 2 + 2 * n * b + 2 * n + b + b ^ 2, by ring⟩
    dsimp only [g]
    rw [← hadd _ _ (by omega) (by omega), ← hadd _ _ (by omega) hb,
      show (2 * n + 1 + 2 * b) ^ 2 + (2 * n + 1) ^ 2 =
        2 * ((2 * n + 1 + b) ^ 2 + b ^ 2) by ring, hf.2 hcop, h2]
  -- With step two the second difference on odd squares is constant.
  have odd (n : ℕ) : g (2 * n + 1) = 1 + f 4 * n * (n + 1) := by
    induction n using Nat.twoStepInduction with
    | zero => simpa using h1
    | one =>
      have h := shift 0 1 (by decide)
      change g 3 + g 1 = 2 * (f 4 + g 1) at h
      simp only [h1] at h
      norm_num
      linear_combination h
    | more n ih₀ ih₁ =>
      have h := shift n 2 (by decide)
      rw [show 2 * n + 1 + 2 * 2 = 2 * (n + 2) + 1 by omega,
        show 2 * n + 1 + 2 = 2 * (n + 1) + 1 by omega, ih₀, ih₁] at h
      change g (2 * (n + 2) + 1) + _ = 2 * (_ + f 4) at h
      push_cast at h ⊢
      linear_combination h
  refine ⟨odd, ?_⟩
  intro n
  cases n with
  | zero => simp
  | succ n =>
    have h := shift n 1 (by decide)
    rw [show 2 * n + 1 + 2 * 1 = 2 * (n + 1) + 1 by omega,
      show 2 * n + 1 + 1 = 2 * (n + 1) by omega, odd, odd, h1] at h
    change g (2 * (n + 1)) = f 4 * ((n + 1 : ℕ) : ℂ) ^ 2
    push_cast at h ⊢
    linear_combination -h / 2

end multiplicative_additive_on_squares

/-- **Multiplicative functions additive on pairs of squares.** Let $f$ be a complex-valued
multiplicative arithmetic function (so $f(1) = 1$ and $f(ab) = f(a) f(b)$ for coprime $a$ and
$b$) such that $f(m^2 + n^2) = f(m^2) + f(n^2)$ for all positive integers $m$ and $n$. Then
$f(4)$ is $0$ or $4$; $f(q^{2k}) = f(q^2)^k$ for all positive integers $q$ and $k$; and if
$f(4) = 4$, then $f(m^2) = m^2$ for every positive integer $m$.

The source also assumes $f \ne 0$, which follows from $f(1) = 1$.

Source: Elchin Hasanalizade, *On the k-Additive Uniqueness of Sums of Consecutive Squares
for Multiplicative Functions*, INTEGERS 25 (2025), Article A40, Theorem 1
(`integers-2025-A40-thm-1`). -/
public theorem multiplicative_additive_on_squares (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hadd : ∀ m n : ℕ, 0 < m → 0 < n → f (m ^ 2 + n ^ 2) = f (m ^ 2) + f (n ^ 2)) :
    (f 4 = 0 ∨ f 4 = 4) ∧
      (∀ q k : ℕ, 0 < q → 0 < k → f (q ^ (2 * k)) = f (q ^ 2) ^ k) ∧
      (f 4 = 4 → ∀ m : ℕ, 0 < m → f (m ^ 2) = (m : ℂ) ^ 2) := by
  obtain ⟨odd, even⟩ := multiplicative_additive_on_squares.square_values f hf hadd
  -- At 36 the even-square formula must agree with the product of the values at 4 and 9.
  have h36 := hf.2 (by decide : Nat.Coprime 4 9)
  rw [show 4 * 9 = (2 * 3) ^ 2 by decide, even,
    show 9 = (2 * 1 + 1) ^ 2 by decide, odd] at h36
  push_cast at h36
  have hroots : f 4 * (f 4 - 4) = 0 := by linear_combination -h36 / 2
  have hcases : f 4 = 0 ∨ f 4 = 4 := (mul_eq_zero.mp hroots).imp_right sub_eq_zero.mp
  have squares (h4 : f 4 = 4) (n : ℕ) : f (n ^ 2) = (n : ℂ) ^ 2 := by
    obtain ⟨r, rfl | rfl⟩ := n.even_or_odd'
    · rw [even, h4]
      push_cast
      ring
    · rw [odd, h4]
      push_cast
      ring
  refine ⟨hcases, ?_, fun h4 m _ => squares h4 m⟩
  intro q k _ hk
  rw [Nat.mul_comm, pow_mul]
  rcases hcases with h0 | h4
  · have parity (n : ℕ) : f (n ^ 2) = (n % 2 : ℕ) := by
      obtain ⟨r, rfl | rfl⟩ := n.even_or_odd'
      · simp [even, h0]
      · simp [odd, h0, Nat.add_mod]
    rw [parity, parity, Nat.pow_mod]
    rcases Nat.mod_two_eq_zero_or_one q with hq | hq <;> simp [hq, hk.ne']
  · rw [squares h4, squares h4, Nat.cast_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]

namespace consecutiveSquareSums

private def block (a l : ℕ) : ℕ := ∑ i ∈ Finset.range l, (a + i + 1) ^ 2

private def IsBlock (x : ℕ) : Prop := ∃ a l : ℕ, 0 < l ∧ x = block a l

private theorem block_succ (a l : ℕ) :
    block a (l + 1) = block a l + (a + l + 1) ^ 2 := Finset.sum_range_succ _ _

private theorem block_one (a : ℕ) : block a 1 = (a + 1) ^ 2 := by
  delta block
  simp

private theorem block_add (a l m : ℕ) :
    block a (l + m) = block a l + block (a + l) m := by
  delta block
  simp only [Finset.sum_range_add, Nat.add_assoc]

private theorem block_eq_Ioc (a l : ℕ) :
    block a l = ∑ j ∈ Finset.Ioc a (a + l), j ^ 2 := by
  induction l with
  | zero =>
    delta block
    simp
  | succ l ih =>
    rw [block_succ, show a + (l + 1) = a + l + 1 by omega,
      Finset.sum_Ioc_succ_top (Nat.le_add_right a l), ih]

/-- Padding both sides of an equal-sum relation with ones keeps the relation valid. -/
private theorem equal_pair_sums (k : ℕ) (hk : 2 ≤ k) (f : ArithmeticFunction ℂ)
    (hadd : ∀ x : Fin k → ℕ, (∀ i, ∃ m n : ℕ, n < m ∧ x i = ∑ j ∈ Finset.Ioc n m, j ^ 2) →
      f (∑ i, x i) = ∑ i, f (x i)) {a b c d : ℕ}
    (ha : IsBlock a) (hb : IsBlock b) (hc : IsBlock c) (hd : IsBlock d) (h : a + b = c + d) :
    f a + f b = f c + f d := by
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, k = 2 + r := ⟨k - 2, by omega⟩
  have eval (a b : ℕ) (ha : IsBlock a) (hb : IsBlock b) :
      f (a + b + r) = f a + f b + r • f 1 := by
    let x (i : ℕ) := if i = 0 then a else if i = 1 then b else 1
    have hx (i : Fin (2 + r)) : ∃ m n : ℕ, n < m ∧ x i = ∑ j ∈ Finset.Ioc n m, j ^ 2 := by
      have b1 : IsBlock 1 := ⟨0, 1, by decide, by simp [block_one]⟩
      have hxi : IsBlock (x i) := by
        dsimp only [x]
        split_ifs <;> assumption
      obtain ⟨l, m, hm, he⟩ := hxi
      exact ⟨l + m, l, by omega, he.trans (block_eq_Ioc l m)⟩
    have hs (u : ℕ) : x (2 + u) = 1 := by
      simp [x, show 2 + u ≠ 1 by omega]
    have sums {R : Type} [AddCommMonoid R] (g : ℕ → R) :
        ∑ i : Fin (2 + r), g (x i) = g a + g b + r • g 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => g (x i)), Finset.sum_range_add]
      simp [hs, Finset.sum_range_succ, x]
    have hsum := sums (R := ℕ) id
    simp only [id_eq, nsmul_eq_mul, Nat.cast_id, mul_one] at hsum
    have hadd' := hadd (fun i => x i) hx
    rw [hsum, sums f] at hadd'
    exact hadd'
  have h₁ := eval a b ha hb
  have h₂ := eval c d hc hd
  rw [h, h₂] at h₁
  exact add_right_cancel h₁.symm

/-- The defect at length two is independent of the starting point; the defect at any nonempty
length is the same defect times the number of joins. Exact `k`-additivity makes it zero. -/
private theorem map_block (k : ℕ) (hk : 2 ≤ k) (f : ArithmeticFunction ℂ)
    (hadd : ∀ x : Fin k → ℕ, (∀ i, ∃ m n : ℕ, n < m ∧ x i = ∑ j ∈ Finset.Ioc n m, j ^ 2) →
      f (∑ i, x i) = ∑ i, f (x i)) (a l : ℕ) :
    f (block a l) = ∑ i ∈ Finset.range l, f ((a + i + 1) ^ 2) := by
  let error := f (block 0 2) - f 1 - f 4
  have compare (a l : ℕ) (hl : 0 < l) :
      f (block a (l + 1)) + f ((a + l + 2) ^ 2) = f (block a l) + f (block (a + l) 2) := by
    have he : block a (l + 1) + block (a + (l + 1)) 1 = block a l + block (a + l) 2 := by
      rw [← block_add, ← block_add]
    simpa only [block_one, Nat.add_assoc] using equal_pair_sums k hk f hadd
      ⟨a, l + 1, Nat.succ_pos _, rfl⟩ ⟨_, 1, Nat.one_pos, rfl⟩
      ⟨a, l, hl, rfl⟩ ⟨_, 2, by decide, rfl⟩ he
  have two (a : ℕ) : f (block a 2) = f ((a + 1) ^ 2) + f ((a + 2) ^ 2) + error := by
    induction a with
    | zero =>
      dsimp [error]
      ring
    | succ a ih =>
      have h := compare a 1 Nat.one_pos
      rw [block_one, ih] at h
      linear_combination -h
  have map_succ (l : ℕ) : ∀ a : ℕ,
      f (block a (l + 1)) = ∑ i ∈ Finset.range (l + 1), f ((a + i + 1) ^ 2) + l • error := by
    induction l with
    | zero => intro a; simp [block_one]
    | succ l ih =>
      intro a
      have h := compare a (l + 1) (Nat.succ_pos _)
      rw [ih, two] at h
      rw [Finset.sum_range_succ, succ_nsmul]
      linear_combination h
  have hfull : f (block 0 k) = ∑ i ∈ Finset.range k, f ((0 + i + 1) ^ 2) := by
    have h := hadd (fun i => (0 + i.val + 1) ^ 2) (fun i =>
      ⟨i.val + 1, i.val, Nat.lt_succ_self _, by simp [Nat.Ioc_succ_singleton]⟩)
    rw [Fin.sum_univ_eq_sum_range (fun i => (0 + i + 1) ^ 2),
      Fin.sum_univ_eq_sum_range (fun i => f ((0 + i + 1) ^ 2))] at h
    exact h
  have herror : error = 0 := by
    have h := map_succ (k - 1) 0
    rw [show k - 1 + 1 = k by omega, hfull, nsmul_eq_mul] at h
    have he : ((k - 1 : ℕ) : ℂ) * error = 0 := by linear_combination -h
    exact (mul_eq_zero.mp he).resolve_left (Nat.cast_ne_zero.mpr (by omega))
  cases l with
  | zero =>
    delta block
    simp
  | succ l => simp [map_succ, herror]

/-- An equal-sum relation among four blocks gives a recurrence for the square values. -/
private theorem map_square (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (pair : ∀ {a b c d : ℕ}, IsBlock a → IsBlock b → IsBlock c → IsBlock d →
      a + b = c + d → f a + f b = f c + f d)
    (mapBlock : ∀ a l : ℕ, f (block a l) = ∑ i ∈ Finset.range l, f ((a + i + 1) ^ 2)) :
    ∀ n : ℕ, f (n ^ 2) = (n : ℂ) ^ 2 := by
  let q (n : ℕ) := f (n ^ 2)
  have h1 : q 1 = 1 := by simpa [q] using hf.map_one
  have step (n : ℕ) : q (n + 1) + q (n + 4) = q (n + 2) + q (n + 3) + q 2 := by
    have he : block n 1 + block (n + 3) 1 = block (n + 1) 2 + block 1 1 := by
      rw [show block (n + 1) 2 = (n + 2) ^ 2 + (n + 3) ^ 2 by rw [block_succ, block_one]]
      simp only [block_one]
      ring
    have he' := pair ⟨n, 1, by decide, rfl⟩ ⟨n + 3, 1, by decide, rfl⟩
      ⟨n + 1, 2, by decide, rfl⟩ ⟨1, 1, by decide, rfl⟩ he
    rw [mapBlock (n + 1) 2] at he'
    simpa [block_one, Finset.sum_range_succ, q] using he'
  have h6 : q 6 = q 2 * q 3 := by
    simpa [q] using hf.map_mul_of_coprime (by decide : Nat.Coprime 4 9)
  have h10 : q 10 = q 2 * q 5 := by
    simpa [q] using hf.map_mul_of_coprime (by decide : Nat.Coprime 4 25)
  have s0 : q 1 + q 4 = q 2 + q 3 + q 2 := step 0
  have s1 : q 2 + q 5 = q 3 + q 4 + q 2 := step 1
  have s2 : q 3 + q 6 = q 4 + q 5 + q 2 := step 2
  have s3 : q 4 + q 7 = q 5 + q 6 + q 2 := step 3
  have s4 : q 5 + q 8 = q 6 + q 7 + q 2 := step 4
  have s5 : q 6 + q 9 = q 7 + q 8 + q 2 := step 5
  have s6 : q 7 + q 10 = q 8 + q 9 + q 2 := step 6
  have h5 : q 5 = 2 * q 2 + 2 * q 3 - 1 := by linear_combination s0 + s1 - h1
  have e6 : q 2 * q 3 = 5 * q 2 + 2 * q 3 - 2 := by
    linear_combination 2 * s0 + s1 + s2 - 2 * h1 - h6
  have e10 : q 2 * q 5 = 17 * q 2 + 4 * q 3 - 4 := by
    linear_combination 4 * s0 + 3 * s1 + 3 * s2 + 2 * s3 + 2 * s4 + s5 + s6 - 4 * h1 - h10
  have roots : q 2 * (q 2 - 4) = 0 := by
    linear_combination (e10 - q 2 * h5 - 2 * e6) / 2
  have h2 : q 2 = 4 := by
    rcases mul_eq_zero.mp roots with h0 | h4
    · have h3 : q 3 = 1 := by rw [h0] at e6; linear_combination -e6 / 2
      have h140 : f (block 0 7) = 0 := by
        change f (140 : ℕ) = 0
        rw [show (140 : ℕ) = 4 * 35 by decide, hf.map_mul_of_coprime (by decide),
          ← show q 2 = f 4 from rfl, h0, zero_mul]
      rw [mapBlock] at h140
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h140
      change q 1 + q 2 + q 3 + q 4 + q 5 + q 6 + q 7 = 0 at h140
      have contradiction : (4 : ℂ) = 0 := by
        linear_combination h140 - 6 * s0 - 4 * s1 - 2 * s2 - s3 + 5 * h1 - 16 * h0 - 9 * h3
      exact (by norm_num : (4 : ℂ) ≠ 0) contradiction |>.elim
    · exact sub_eq_zero.mp h4
  have h3 : q 3 = 9 := by rw [h2] at e6; linear_combination e6 / 2
  change ∀ n, q n = (n : ℂ) ^ 2
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    obtain _ | _ | _ | _ | n := n
    · simp [q]
    · simpa using h1
    · norm_num
      exact h2
    · norm_num
      exact h3
    · have h := step n
      rw [ih (n + 1) (by omega), ih (n + 2) (by omega), ih (n + 3) (by omega), h2] at h
      push_cast at h ⊢
      linear_combination h

-- Clearing the denominator in the square-pyramidal sum also works for shifted blocks.
private theorem six_mul_block (a l : ℕ) :
    6 * block a l = l * (6 * a ^ 2 + 6 * a * (l + 1) + (l + 1) * (2 * l + 1)) := by
  induction l with
  | zero =>
    delta block
    simp
  | succ l ih =>
    rw [block_succ, Nat.mul_add, ih]
    ring

/-- For odd `n = 2*m+3`, compare a block of length 6 with one of length `6*n`. The block
centres differ by one, offsetting the change in the mean of the squared deviations. -/
private theorem odd_multiple_six (m : ℕ) :
    let n := 2 * m + 3
    let a := 6 * m ^ 2 + 18 * m + 9
    let b := 6 * m ^ 2 + 12 * m + 2
    block b (6 * n) = n * block a 6 ∧
      2 * block a 6 = n ^ 2 * (108 * m ^ 2 + 324 * m + 207) + 47 := by
  dsimp only
  constructor
  · apply Nat.mul_left_cancel (by decide : 0 < 6)
    rw [six_mul_block, Nat.mul_left_comm 6 (2 * m + 3), six_mul_block]
    ring
  · apply Nat.mul_left_cancel (by decide : 0 < 6)
    rw [mul_left_comm, six_mul_block]
    ring

/-- The same comparison at length 12 gives a multiplier with a different residue modulo `n`. -/
private theorem odd_multiple_twelve (m : ℕ) :
    let n := 2 * m + 3
    let a := 24 * m ^ 2 + 72 * m + 42
    let b := 24 * m ^ 2 + 60 * m + 29
    block b (12 * n) = n * block a 12 ∧
      block a 12 = n ^ 2 * (1728 * m ^ 2 + 5184 * m + 3096) + 506 := by
  dsimp only
  constructor
  · apply Nat.mul_left_cancel (by decide : 0 < 6)
    rw [six_mul_block, Nat.mul_left_comm 6 (2 * m + 3), six_mul_block]
    ring
  · apply Nat.mul_left_cancel (by decide : 0 < 6)
    rw [six_mul_block]
    ring

private theorem eq_id_of_blocks (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hblock : ∀ a l : ℕ, f (block a l) = block a l) : ∀ n : ℕ, f n = n := by
  have extract {n a l b r : ℕ} (he : block b r = n * block a l) (hc : n.Coprime (block a l))
      (hpos : 0 < block a l) : f n = n := by
    have h := hblock b r
    rw [he, hf.map_mul_of_coprime hc, hblock, Nat.cast_mul] at h
    exact mul_right_cancel₀ (by exact_mod_cast hpos.ne') h
  have oddPower {p e : ℕ} (hp : p.Prime) (ho : p % 2 = 1) (he : 0 < e) :
      f (p ^ e) = (p ^ e : ℕ) := by
    have hn : (p ^ e) % 2 = 1 := by simp [Nat.pow_mod, ho]
    have hge : 2 ≤ p ^ e := hp.two_le.trans (Nat.le_self_pow he.ne' _)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, p ^ e = 2 * m + 3 := ⟨(p ^ e - 3) / 2, by omega⟩
    -- The exceptional prime for the first multiplier cannot divide the second residue.
    by_cases h47 : p ∣ 47
    · obtain ⟨hprod, hres⟩ := odd_multiple_twelve m
      rw [← hm] at hprod hres
      refine extract hprod ((hp.coprime_iff_not_dvd.mpr ?_).pow_left e) (by omega)
      intro hd
      have hpN : p ∣ p ^ e := dvd_pow_self _ he.ne'
      have hpd : p ∣ (p ^ e) ^ 2 * (1728 * m ^ 2 + 5184 * m + 3096) :=
        dvd_mul_of_dvd_left (hpN.trans (dvd_pow_self _ (by decide))) _
      rw [hres, ← Nat.dvd_add_iff_right hpd] at hd
      have hg := Nat.dvd_gcd h47 hd
      rw [show Nat.gcd 47 506 = 1 by decide] at hg
      exact hp.not_dvd_one hg
    · obtain ⟨hprod, hres⟩ := odd_multiple_six m
      rw [← hm] at hprod hres
      refine extract hprod ((hp.coprime_iff_not_dvd.mpr ?_).pow_left e) (by omega)
      intro hd
      have hpN : p ∣ p ^ e := dvd_pow_self _ he.ne'
      have hpd : p ∣ (p ^ e) ^ 2 * (108 * m ^ 2 + 324 * m + 207) :=
        dvd_mul_of_dvd_left (hpN.trans (dvd_pow_self _ (by decide))) _
      apply h47
      rw [Nat.dvd_add_iff_right hpd, ← hres]
      exact dvd_mul_of_dvd_right hd _
  have oddFixed : ∀ n : ℕ, Odd n → f n = n := by
    apply Nat.recOnPosPrimePosCoprime
    · intro p e hp he ho
      rcases hp.eq_two_or_odd with rfl | hpodd
      · rw [Nat.odd_iff, Nat.pow_mod] at ho
        simp [zero_pow he.ne'] at ho
      · exact oddPower hp hpodd he
    · simp
    · simp [hf.map_one]
    · intro a b _ _ hc ha hb hodd
      obtain ⟨hao, hbo⟩ := Nat.odd_mul.mp hodd
      rw [hf.map_mul_of_coprime hc, ha hao, hb hbo, Nat.cast_mul]
  apply Nat.recOnPosPrimePosCoprime
  · intro p e hp he
    rcases hp.eq_two_or_odd with rfl | hpodd
    · -- A prefix of length `6*n` has value `n * (6*n+1) * (12*n+1)`; the latter factors are odd.
      let n := 2 ^ e
      let u := 6 * n + 1
      let v := 12 * n + 1
      have hu : Odd u := ⟨3 * n, by dsimp [u]; ring⟩
      have hv : Odd v := ⟨6 * n, by dsimp [v]; ring⟩
      have hc : n.Coprime (u * v) :=
        ((Nat.coprime_two_left.mpr hu).mul_right (Nat.coprime_two_left.mpr hv)).pow_left e
      have hprod : block 0 (6 * n) = n * (u * v) := by
        apply Nat.mul_left_cancel (by decide : 0 < 6)
        rw [six_mul_block]
        dsimp [u, v]
        ring
      have h := hblock 0 (6 * n)
      rw [hprod, hf.map_mul_of_coprime hc, oddFixed (u * v) (hu.mul hv)] at h
      rw [Nat.cast_mul (α := ℂ) n (u * v)] at h
      have hpos : 0 < u * v := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
      exact mul_right_cancel₀ (Nat.cast_ne_zero.mpr hpos.ne') h
    · exact oddPower hp hpodd he
  · simp
  · simpa using hf.map_one
  · intro a b _ _ hc ha hb
    rw [hf.map_mul_of_coprime hc, ha, hb, Nat.cast_mul]

end consecutiveSquareSums

/-- **Sums of consecutive squares form a $k$-additive uniqueness set for every $k \ge 2$.** Let
$k \ge 2$, and call a natural number a sum of consecutive squares if it equals
$(n+1)^2 + (n+2)^2 + \dots + m^2$ for some natural numbers $n < m$. Let $f$ be a complex-valued
multiplicative arithmetic function (so $f(1) = 1$ and $f(ab) = f(a) f(b)$ for coprime $a$ and
$b$). If $f(x_1 + \dots + x_k) = f(x_1) + \dots + f(x_k)$ for all sums of consecutive squares
$x_1, \dots, x_k$, then $f(n) = n$ for every natural number $n$.

Source: Elchin Hasanalizade, *On the k-Additive Uniqueness of Sums of Consecutive Squares
for Multiplicative Functions*, INTEGERS 25 (2025), Article A40, Theorem 2
(`integers-2025-A40-thm-2`). -/
public theorem consecutiveSquareSums_kAdditiveUniqueness (k : ℕ) (hk : 2 ≤ k)
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ x : Fin k → ℕ, (∀ i, ∃ m n : ℕ, n < m ∧ x i = ∑ j ∈ Finset.Ioc n m, j ^ 2) →
      f (∑ i, x i) = ∑ i, f (x i)) :
    ∀ n : ℕ, f n = n := by
  have hblock := consecutiveSquareSums.map_block k hk f hadd
  have hsq := consecutiveSquareSums.map_square f hf
    (consecutiveSquareSums.equal_pair_sums k hk f hadd) hblock
  apply consecutiveSquareSums.eq_id_of_blocks f hf
  intro a l
  rw [hblock]
  delta consecutiveSquareSums.block
  simp only [hsq, Nat.cast_sum, Nat.cast_pow]

end MetaMathlibExt
