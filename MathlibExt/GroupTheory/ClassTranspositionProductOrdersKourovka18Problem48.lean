/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Iterate
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Orders of products of two class transpositions (Kourovka Notebook Problem 18.48)

This file proves that only finitely many positive integers are orders of products of two
class transpositions of the integers.

Kourovka Notebook, Problem 18.48 (S. Kohl), marked solved in the 21st issue: is it true that there
are only finitely many integers which occur as orders of products of two class transpositions? (For
the definition, see 17.57.)

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.48 (S. Kohl). UnsolvedMath record
UM-00701477 (`KOU-18.48`), dataset ulamai/UnsolvedMath v1.8.0.

Kourovka 17.57: for `0 ≤ r < m` let `r(m) = {r + k m | k ∈ ℤ}`; for disjoint `r₁(m₁)`, `r₂(m₂)` the
class transposition `τ_{r₁(m₁), r₂(m₂)}` interchanges `r₁ + k m₁` and `r₂ + k m₂` for each `k ∈ ℤ`
and fixes everything else (the encoding of the OpenConjectures entry
`Kourovka2175ClassTranspositionSubgroups`). Orders are positive integers; products of infinite order
(`orderOf = 0`) do not count.

The proof uses Iskra's obstruction to eight consecutive steps of a simple alternating path
(arXiv:2610.01793, Sections 4–6). Each vertex then has at most sixteen reachable endpoints,
counted by path length and starting transposition. Thus each point period divides `16!`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.ClassTranspositionProductOrdersKourovka18Problem48Wanted
open Function

/-- **Residue class.** For integers $r$ and $m$, the residue class $r(m)$ is the set
$\{x \in \mathbb{Z} : x \equiv r \pmod{m}\} = \{r + k m : k \in \mathbb{Z}\}$. -/
def resClass (r m : ℤ) : Set ℤ := {x | x ≡ r [ZMOD m]}

/-- **Class transposition of two residue classes.** For integers $r_1, m_1, r_2, m_2$, write
$r_1(m_1) = r_1 + m_1\mathbb{Z}$ and $r_2(m_2) = r_2 + m_2\mathbb{Z}$ for the residue classes. A
permutation $\sigma$ of $\mathbb{Z}$ is the class transposition $\tau_{r_1(m_1), r_2(m_2)}$ when
$0 \le r_1 < m_1$ and $0 \le r_2 < m_2$, the residue classes $r_1(m_1)$ and $r_2(m_2)$ are
disjoint, $\sigma$ interchanges $r_1 + k m_1$ and $r_2 + k m_2$ for every integer $k$, and
$\sigma$ fixes every integer outside $r_1(m_1) \cup r_2(m_2)$.

This is the definition of class transpositions in Kourovka Problem 17.57. -/
def IsClassTrans (σ : Equiv.Perm ℤ) (r₁ m₁ r₂ m₂ : ℤ) : Prop :=
  0 ≤ r₁ ∧ r₁ < m₁ ∧ 0 ≤ r₂ ∧ r₂ < m₂ ∧ 0 < m₁ ∧ 0 < m₂ ∧
  Disjoint (resClass r₁ m₁) (resClass r₂ m₂) ∧
  (∀ k : ℤ, σ (r₁ + k * m₁) = r₂ + k * m₂ ∧ σ (r₂ + k * m₂) = r₁ + k * m₁) ∧
  ∀ x : ℤ, x ∉ resClass r₁ m₁ → x ∉ resClass r₂ m₂ → σ x = x

/-- **Class transpositions of the integers.** A permutation $\sigma$ of $\mathbb{Z}$ is a class
transposition when it is the class transposition $\tau_{r_1(m_1), r_2(m_2)}$ for some integers
$r_1, m_1, r_2, m_2$. -/
def IsClassTransposition (σ : Equiv.Perm ℤ) : Prop :=
  ∃ r₁ m₁ r₂ m₂ : ℤ, IsClassTrans σ r₁ m₁ r₂ m₂

/-- **Claim of Kourovka Problem 18.48.** Only finitely many positive integers occur as orders of
products $\sigma\tau$ of two class transpositions $\sigma$ and $\tau$ of $\mathbb{Z}$. -/
def classTranspositionProductOrdersFinite : Prop :=
  {k : ℕ | 0 < k ∧ ∃ σ τ : Equiv.Perm ℤ, IsClassTransposition σ ∧ IsClassTransposition τ ∧
    orderOf (σ * τ) = k}.Finite


private theorem homogeneous_chain (p q : ℤ) {n i : ℕ} (hi : i < n) :
    p * (p ^ i * q ^ (n - i)) = q * (p ^ (i + 1) * q ^ (n - (i + 1))) := by
  have h : n - i = (n - (i + 1)) + 1 := by omega
  rw [h, pow_succ, pow_succ p]
  ring

-- Bézout permits extending a chain after translating it by a homogeneous solution.
private theorem exists_chain {p q : ℤ} (hcop : IsCoprime p q) (n : ℕ) :
    ∃ t : ℕ → ℤ, ∀ i < n, q * t (i + 1) = q + p * t i := by
  induction n with
  | zero => exact ⟨fun _ => 0, by simp⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨a, b, hab⟩ : IsCoprime (p ^ (n + 1)) q := hcop.pow_left
    let z := -p * t n * a
    refine ⟨fun i => if i ≤ n then t i + p ^ i * q ^ (n - i) * z
      else 1 + -p * t n * (-b), ?_⟩
    intro i hi
    by_cases hin : i < n
    · simp only [ite_eq_left (show i ≤ n by omega), ite_eq_left (show i + 1 ≤ n by omega)]
      linear_combination ht i hin - homogeneous_chain p q hin * z
    · have hi' : i = n := by omega
      subst i
      simp only [Nat.le_refl, ite_true, Nat.sub_self, pow_zero, mul_one,
        ite_eq_right (Nat.not_succ_le_self n), z]
      rw [show p * (t n + p ^ n * (-p * t n * a)) =
          p * t n * (1 - a * p ^ (n + 1)) by rw [pow_succ]; ring]
      linear_combination (p * t n) * hab

-- A positive-slope affine branch cannot map one point of its domain to the next
-- point of the same domain when the permutation has finite order.
private theorem not_finite_affine_branch {g : Equiv.Perm ℤ} {n : ℕ}
    (hn : 0 < n) (hg : g ^ n = 1) {A B D : ℤ} (hBD : 0 < B * D)
    (hmap : ∀ t : ℤ, g (A + B * t) = A + B + D * t) : False := by
  have hB : B ≠ 0 := by rintro rfl; simp at hBD
  have hD : D ≠ 0 := by rintro rfl; simp at hBD
  obtain ⟨d, p, q, _, hpq, hp, hq⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left B hD)
  have hq₀ : q ≠ 0 := by intro h; apply hB; simp [hq, h]
  have hs : 0 < (p : ℚ) / q := by
    have hh : 0 < (p * q) * (d : ℤ) ^ 2 := by
      calc
        0 < B * D := hBD
        _ = (p * q) * (d : ℤ) ^ 2 := by rw [hq, hp]; ring
    have hsign : 0 < p * q := pos_of_mul_pos_left hh (sq_nonneg _)
    have hsign' : 0 < (p : ℚ) * (q : ℚ) := by exact_mod_cast hsign
    exact div_pos_iff.mpr (mul_pos_iff.mp hsign')
  let F : ℚ → ℚ := fun x => 1 + (p : ℚ) / q * x
  have hF : StrictMono F := fun _ _ h => add_lt_add_right (mul_lt_mul_of_pos_left h hs) 1
  have chain_fixed (t : ℕ → ℤ) (ht : ∀ i < n, q * t (i + 1) = q + p * t i) :
      t 1 = t 0 := by
    have hstep (i : ℕ) (hi : i < n) :
        g (A + B * t i) = A + B * t (i + 1) := by
      rw [hmap, hq, hp]
      linear_combination -(d : ℤ) * ht i hi
    have hstep' (i : ℕ) (hi : i < n) : F (t i) = t (i + 1) := by
      have hcast : (q : ℚ) * (t (i + 1) : ℚ) = q + (p : ℚ) * (t i : ℚ) := by
        exact_mod_cast ht i hi
      dsimp [F]
      field_simp [show (q : ℚ) ≠ 0 by exact_mod_cast hq₀]
      linear_combination -hcast
    have hrun (i : ℕ) (hi : i ≤ n) :
        (g ^ i) (A + B * t 0) = A + B * t i ∧ F^[i] (t 0 : ℚ) = t i := by
      induction i with
      | zero => simp
      | succ i ih =>
        obtain ⟨h₁, h₂⟩ := ih (by omega)
        constructor
        · rw [pow_succ', Equiv.Perm.mul_apply, h₁, hstep i (by omega)]
        · rw [iterate_succ_apply', h₂, hstep' i (by omega)]
    obtain ⟨h₁, h₂⟩ := hrun n le_rfl
    rw [hg, Equiv.Perm.one_apply] at h₁
    have he : t n = t 0 := by
      apply mul_left_cancel₀ hB
      omega
    rw [he] at h₂
    have hf₀ : F (t 0) = (t 0 : ℚ) := by
      rcases lt_trichotomy (t 0 : ℚ) (F (t 0)) with h | h | h
      · have := (hF.strictMono_iterate_of_lt_map h) hn
        simp [h₂] at this
      · exact h.symm
      · have := (hF.strictAnti_iterate_of_map_lt h) hn
        simp [h₂] at this
    exact_mod_cast (hstep' 0 hn).symm.trans hf₀
  obtain ⟨t, ht⟩ := exists_chain (Int.isCoprime_iff_gcd_eq_one.mpr hpq) n
  let u (i : ℕ) := t i + p ^ i * q ^ (n - i)
  have hu : ∀ i < n, q * u (i + 1) = q + p * u i := by
    intro i hi
    dsimp [u]
    linear_combination ht i hi - homogeneous_chain p q hi
  have ht₀ := chain_fixed t ht
  have hu₀ := chain_fixed u hu
  have he : p = q := by
    have h : n = (n - 1) + 1 := by omega
    apply mul_right_cancel₀ (pow_ne_zero (n - 1) hq₀)
    simp only [u, ht₀, pow_one, pow_zero, one_mul, Nat.sub_zero] at hu₀
    have hpow := pow_succ q (n - 1)
    rw [← h] at hpow
    rw [hpow] at hu₀
    rw [mul_comm q (q ^ (n - 1))]
    omega
  have h := ht 0 hn
  rw [ht₀, he] at h
  exact hq₀ (by omega)

-- The first Boolean selects the permutation and the second selects one of its classes.
private structure TranspositionPair where
  perm : Bool → Equiv.Perm ℤ
  residue : Bool → Bool → ℤ
  modulus : Bool → Bool → ℤ
  spec : ∀ c, IsClassTrans (perm c) (residue c false) (modulus c false)
    (residue c true) (modulus c true)

private def TranspositionPair.point (P : TranspositionPair) (c s : Bool) (k : ℤ) : ℤ :=
  P.residue c s + k * P.modulus c s

private theorem TranspositionPair.modulus_pos (P : TranspositionPair) (c s : Bool) :
    0 < P.modulus c s := by
  cases s
  · exact (P.spec c).2.2.2.2.1
  · exact (P.spec c).2.2.2.2.2.1

private theorem TranspositionPair.apply_point (P : TranspositionPair) (c s : Bool) (k : ℤ) :
    P.perm c (P.point c s k) = P.point c (!s) k := by
  have h := (P.spec c).2.2.2.2.2.2.2.1 k
  cases s
  · exact h.1
  · exact h.2

private theorem mem_resClass_iff (x r m : ℤ) :
    x ∈ resClass r m ↔ ∃ k : ℤ, x = r + k * m := by
  change (x ≡ r [ZMOD m]) ↔ _
  rw [Int.modEq_iff_dvd, ← Int.dvd_neg]
  simp only [neg_sub]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith only [hk]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩

private theorem TranspositionPair.exists_point (P : TranspositionPair) {c : Bool} {x : ℤ}
    (hx : P.perm c x ≠ x) : ∃ s k, x = P.point c s k := by
  by_cases h₀ : x ∈ resClass (P.residue c false) (P.modulus c false)
  · exact ⟨false, (mem_resClass_iff ..).mp h₀⟩
  by_cases h₁ : x ∈ resClass (P.residue c true) (P.modulus c true)
  · exact ⟨true, (mem_resClass_iff ..).mp h₁⟩
  exact (hx ((P.spec c).2.2.2.2.2.2.2.2 x h₀ h₁)).elim

private theorem TranspositionPair.involutive (P : TranspositionPair) (c : Bool) :
    Involutive (P.perm c) := by
  intro x
  by_cases hx : P.perm c x = x
  · rw [hx, hx]
  · obtain ⟨s, k, rfl⟩ := P.exists_point hx
    rw [P.apply_point, P.apply_point, Bool.not_not]

private def TranspositionPair.product (P : TranspositionPair) (c : Bool) : Equiv.Perm ℤ :=
  P.perm (!c) * P.perm c

private theorem TranspositionPair.product_pow_eq_one (P : TranspositionPair)
    {n : ℕ} (h : (P.product false) ^ n = 1) (c : Bool) : (P.product c) ^ n = 1 := by
  cases c
  · exact h
  · rw [product, show P.perm (!true) * P.perm true = (P.product false)⁻¹ by
          rw [product, mul_inv_rev]
          congr 1 <;> exact Equiv.ext fun x => by
            apply (P.perm _).injective
            exact (P.involutive _ x).trans (Equiv.apply_symm_apply _ _).symm,
        inv_pow, h, inv_one]

private def TranspositionPair.joins (P : TranspositionPair) (c s r : Bool) (x y : ℤ) : Prop :=
  P.point c (!s) x = P.point (!c) r y

private theorem TranspositionPair.joins_interp (P : TranspositionPair) {c s r : Bool}
    {x y u v : ℤ} (hxy : P.joins c s r x y) (huv : P.joins c s r u v) (t : ℤ) :
    P.joins c s r (x + (u - x) * t) (y + (v - y) * t) := by
  unfold joins point at *
  linear_combination (1 - t) * hxy + t * huv

private theorem TranspositionPair.joins_mul_pos (P : TranspositionPair) {c s r : Bool}
    {x y u v a : ℤ} (hxy : P.joins c s r x y) (huv : P.joins c s r u v)
    (h : 0 < a * (u - x)) : 0 < a * (v - y) := by
  have he : P.modulus (!c) r * (a * (v - y)) = P.modulus c (!s) * (a * (u - x)) := by
    unfold joins point at hxy huv
    linear_combination a * (hxy - huv)
  rw [← mul_pos_iff_of_pos_left (P.modulus_pos (!c) r), he]
  exact mul_pos (P.modulus_pos c (!s)) h

private theorem TranspositionPair.product_apply (P : TranspositionPair) {c s r : Bool}
    {x y : ℤ} (hxy : P.joins c s r x y) :
    P.product c (P.point c s x) = P.point (!c) (!r) y := by
  rw [product, Equiv.Perm.mul_apply, apply_point, hxy, apply_point]

private theorem TranspositionPair.no_repeat_two (P : TranspositionPair)
    {n : ℕ} (hn : 0 < n) {c s r : Bool} (hp : (P.product c) ^ n = 1)
    {x y u v : ℤ} (hxy : P.joins c s r x y) (hyu : P.joins (!c) r s y u)
    (huv : P.joins c s r u v) (hxu : x ≠ u) : False := by
  have hsign : 0 < (u - x) * (v - y) :=
    P.joins_mul_pos hxy huv (mul_self_pos.mpr (sub_ne_zero.mpr hxu.symm))
  apply not_finite_affine_branch hn hp
    (A := P.point c s x) (B := (u - x) * P.modulus c s)
    (D := (v - y) * P.modulus (!c) (!r))
  · simpa only [mul_mul_mul_comm] using
      mul_pos hsign (mul_pos (P.modulus_pos c s) (P.modulus_pos (!c) (!r)))
  · intro t
    rw [show P.point c s x + (u - x) * P.modulus c s * t =
      P.point c s (x + (u - x) * t) by unfold point; ring]
    rw [P.product_apply (P.joins_interp hxy huv t)]
    simp only [joins, Bool.not_not] at hyu
    unfold point at *
    linear_combination hyu

private theorem TranspositionPair.no_repeat_four (P : TranspositionPair)
    {n : ℕ} (hn : 0 < n) {c s r t w : Bool} (hp : (P.product c) ^ n = 1)
    {a b d e u v x y : ℤ}
    (hab : P.joins c s r a b) (hbd : P.joins (!c) r t b d)
    (hde : P.joins c t w d e) (heu : P.joins (!c) w s e u)
    (huv : P.joins c s r u v) (hvx : P.joins (!c) r t v x)
    (hxy : P.joins c t w x y) (hau : a ≠ u) : False := by
  have hsign : 0 < (u - a) * (y - e) :=
    P.joins_mul_pos hde hxy (P.joins_mul_pos hbd hvx
      (P.joins_mul_pos hab huv (mul_self_pos.mpr (sub_ne_zero.mpr hau.symm))))
  have hp₂ : ((P.product c) ^ 2) ^ n = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hp, one_pow]
  apply not_finite_affine_branch hn hp₂
    (A := P.point c s a) (B := (u - a) * P.modulus c s)
    (D := (y - e) * P.modulus (!c) (!w))
  · simpa only [mul_mul_mul_comm] using
      mul_pos hsign (mul_pos (P.modulus_pos c s) (P.modulus_pos (!c) (!w)))
  · intro z
    rw [show P.point c s a + (u - a) * P.modulus c s * z =
      P.point c s (a + (u - a) * z) by unfold point; ring]
    rw [pow_two, Equiv.Perm.mul_apply, P.product_apply (P.joins_interp hab huv z)]
    have h := P.joins_interp hbd hvx z
    simp only [joins, Bool.not_not] at h
    rw [h, P.product_apply (P.joins_interp hde hxy z)]
    simp only [joins, Bool.not_not] at heu
    unfold point at *
    linear_combination heu

private theorem dvd_of_coprime_multiples {a b d h : ℤ} (hc : IsCoprime a b)
    (ha : d ∣ a * h) (hb : d ∣ b * h) : d ∣ h := by
  obtain ⟨u, v, huv⟩ := hc
  have hd := dvd_add (dvd_mul_of_dvd_right ha u) (dvd_mul_of_dvd_right hb v)
  convert hd using 1
  linear_combination -h * huv

private theorem exists_linear_solution {a b h : ℤ} (hh : (Int.gcd a b : ℤ) ∣ h) :
    ∃ x y : ℤ, a * x - b * y = h := by
  obtain ⟨z, rfl⟩ := hh
  refine ⟨Int.gcdA a b * z, -Int.gcdB a b * z, ?_⟩
  linear_combination -z * Int.gcd_eq_gcd_ab a b

-- The two overlapping triples can be joined using their common congruence.
private theorem splice {a b c d e f x y z u v w : ℤ} (ha : 0 < a)
    (hxy : a * x - c * y = e) (hyz : d * y - b * z = f)
    (huv : d * u - b * v = f) (hvw : a * v - c * w = e) :
    ∃ X Y Z W : ℤ, a * X - c * Y = e ∧ d * Y - b * Z = f ∧ a * Z - c * W = e := by
  obtain ⟨g, a', c', hg, hac, ham, hcm⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left c ha.ne')
  have hcop := Int.isCoprime_iff_gcd_eq_one.mpr hac
  have hg₀ : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have he : a' * (v - x) = c' * (w - y) := by
    apply mul_right_cancel₀ hg₀
    rw [ham, hcm] at hxy hvw
    linear_combination hvw - hxy
  have hc' : c' ∣ v - x := hcop.symm.dvd_of_dvd_mul_right
    ⟨w - y, by rw [mul_comm]; exact he⟩
  let P := d * a'
  let Q := b * c'
  let G : ℤ := Int.gcd P Q
  have h₁ : G ∣ b * (v - x) := by
    obtain ⟨k, hk⟩ := hc'
    apply (Int.gcd_dvd_right P Q).trans
    exact ⟨k, by rw [hk]; unfold Q; ring⟩
  have eq₂ : b * (v - z) = d * (u - y) := by linear_combination hyz - huv
  have h₂ : G ∣ b * (v - z) := by
    apply dvd_of_coprime_multiples hcop
    · rw [eq₂]
      exact (Int.gcd_dvd_left P Q).trans ⟨u - y, by unfold P; ring⟩
    · exact (Int.gcd_dvd_right P Q).trans ⟨v - z, by unfold Q; ring⟩
  have hh : G ∣ b * (x - z) := by
    convert Int.dvd_sub h₂ h₁ using 1
    ring
  obtain ⟨t, s, hs⟩ := exists_linear_solution hh
  refine ⟨x + c' * t, y + a' * t, x + c' * s, y + a' * s, ?_, ?_, ?_⟩
  · rw [ham, hcm] at hxy ⊢
    linear_combination hxy
  · unfold P Q at hs
    linear_combination hyz + hs
  · rw [ham, hcm] at hxy ⊢
    linear_combination hxy

private theorem TranspositionPair.no_opposite_triples (P : TranspositionPair)
    {n : ℕ} (hn : 0 < n) {c s r : Bool} (hp : (P.product c) ^ n = 1)
    {x y z u v w : ℤ} (hxy : P.joins c s r x y) (hyz : P.joins (!c) r s y z)
    (huv : P.joins (!c) r s u v) (hvw : P.joins c s r v w) (hxz : x ≠ z) : False := by
  let a := P.modulus c (!s)
  let b := P.modulus c s
  let d := P.modulus (!c) (!r)
  let m := P.modulus (!c) r
  let e := P.residue (!c) r - P.residue c (!s)
  let f := P.residue c s - P.residue (!c) (!r)
  have first {X Y : ℤ} : P.joins c s r X Y ↔ a * X - m * Y = e := by
    unfold joins point a m e
    constructor <;> intro h <;> linear_combination h
  have second {X Y : ℤ} : P.joins (!c) r s X Y ↔ d * X - b * Y = f := by
    unfold joins point d b f
    simp only [Bool.not_not]
    constructor <;> intro h <;> linear_combination h
  have hfixed {X Y Z W : ℤ} (h₁ : a * X - m * Y = e) (h₂ : d * Y - b * Z = f)
      (h₃ : a * Z - m * W = e) : X = Z := by
    by_contra h
    exact P.no_repeat_two hn hp (first.mpr h₁) (second.mpr h₂) (first.mpr h₃) h
  obtain ⟨X, Y, Z, W, h₁, h₂, h₃⟩ :=
    splice (P.modulus_pos c (!s)) (first.mp hxy) (second.mp hyz) (second.mp huv) (first.mp hvw)
  have h₀ := hfixed h₁ h₂ h₃
  have hshift : X + m * m * b = Z + m * a * d :=
    hfixed (Y := Y + a * m * b) (W := W + a * a * d)
      (by linear_combination h₁) (by linear_combination h₂) (by linear_combination h₃)
  have hm : 0 < m := P.modulus_pos _ _
  have hslope : m * b = a * d := by
    apply mul_left_cancel₀ hm.ne'
    linear_combination hshift - h₀
  have hdiff : a * d * (x - z) = 0 := by
    rw [← h₀] at h₂
    have hxy' := first.mp hxy
    have hyz' := second.mp hyz
    linear_combination d * (hxy' - h₁) + m * (hyz' - h₂) + (z - X) * hslope
  exact hxz (sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left
    (mul_ne_zero (P.modulus_pos _ _).ne' (P.modulus_pos _ _).ne')))

private def flipFirst (p : Bool × Bool) : Bool × Bool := (!p.1, p.2)
private def flipSecond (p : Bool × Bool) : Bool × Bool := (p.1, !p.2)

private def neighborSides (s t r : Bool) : Bool × Bool :=
  if t then (r, !s) else (!s, r)

private def TranspositionPair.matchesSides (P : TranspositionPair) (c : Bool)
    (p : Bool × Bool) (x : ℤ) : Prop :=
  let G : ℤ := Int.gcd (P.modulus (!c) false) (P.modulus (!c) true)
  G ∣ P.point c false x - P.residue (!c) p.1 ∧
    G ∣ P.point c true x - P.residue (!c) p.2

private theorem TranspositionPair.matches_of_joins (P : TranspositionPair)
    {c s t r : Bool} {x y z : ℤ} (hxy : P.joins c s t x y)
    (hyz : P.joins (!c) t r y z) : P.matchesSides (!c) (neighborSides s t r) y := by
  have hd {a b : Bool} {v : ℤ} (h : P.point (!c) a y = P.point c b v) :
      (Int.gcd (P.modulus c false) (P.modulus c true) : ℤ) ∣
        P.point (!c) a y - P.residue c b := by
    rw [h]
    suffices (Int.gcd (P.modulus c false) (P.modulus c true) : ℤ) ∣ P.modulus c b by
      unfold point
      convert dvd_mul_of_dvd_right this v using 1
      ring
    cases b
    · exact Int.gcd_dvd_left ..
    · exact Int.gcd_dvd_right ..
  unfold joins at hxy hyz
  simp only [Bool.not_not] at hyz
  cases t
  · simpa only [matchesSides, neighborSides, Bool.false_eq_true, ite_false, Bool.not_not,
      Bool.not_false] using And.intro (hd hxy.symm) (hd hyz)
  · simpa only [matchesSides, neighborSides, ite_true, Bool.not_not, Bool.not_true] using
      And.intro (hd hyz) (hd hxy.symm)

-- An affine line of pairs of congruences cannot visit three corners of this rectangle.
private theorem TranspositionPair.no_corner (P : TranspositionPair) {c : Bool}
    {p : Bool × Bool} {x y z : ℤ} (hx : P.matchesSides c p x)
    (hy : P.matchesSides c (flipFirst p) y) (hz : P.matchesSides c (flipSecond p) z) : False := by
  let G : ℤ := Int.gcd (P.modulus (!c) false) (P.modulus (!c) true)
  let R := P.residue (!c)
  let M := P.modulus c
  obtain ⟨g, m, n, _, hmn, hm, hn⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left (M true) (P.modulus_pos c false).ne')
  change M false = m * (g : ℤ) at hm
  have diff {v w : ℤ} {s a b : Bool}
      (hv : G ∣ P.point c s v - R a) (hw : G ∣ P.point c s w - R b) :
      G ∣ (w - v) * M s - (R b - R a) := by
    convert Int.dvd_sub hw hv using 1
    unfold point R M
    ring
  have hy₀ : G ∣ (y - x) * M false - (R (!p.1) - R p.1) := diff hx.1 hy.1
  have hy₁ : G ∣ (y - x) * M true := by simpa [flipFirst] using diff hx.2 hy.2
  have hz₀ : G ∣ (z - x) * M false := by simpa [flipSecond] using diff hx.1 hz.1
  have hz₁ : G ∣ (z - x) * M true - (R (!p.2) - R p.2) := diff hx.2 hz.2
  have h₁ : G ∣ n * (R (!p.1) - R p.1) := by
    convert Int.dvd_sub (dvd_mul_of_dvd_right hy₁ m) (dvd_mul_of_dvd_right hy₀ n) using 1
    rw [hm, hn]
    ring
  have h₂ : G ∣ m * (R (!p.2) - R p.2) := by
    convert Int.dvd_sub (dvd_mul_of_dvd_right hz₀ n) (dvd_mul_of_dvd_right hz₁ m) using 1
    rw [hm, hn]
    ring
  have normalize {s : Bool} {k : ℤ} (h : G ∣ k * (R (!s) - R s)) :
      G ∣ k * (R false - R true) := by
    cases s
    · rw [show k * (R false - R true) = -(k * (R true - R false)) by ring, Int.dvd_neg]
      exact h
    · exact h
  have hd := dvd_of_coprime_multiples (Int.isCoprime_iff_gcd_eq_one.mpr hmn)
    (normalize h₂) (normalize h₁)
  have hG : (Int.gcd (P.modulus (!c) true) (P.modulus (!c) false) : ℤ) ∣ R false - R true := by
    rw [Int.gcd_comm]
    exact hd
  obtain ⟨u, v, huv⟩ := exists_linear_solution hG
  have he : P.point (!c) false v = P.point (!c) true u := by
    unfold point
    unfold R at huv
    linear_combination -huv
  have hs := (P.spec (!c)).2.2.2.2.2.2.1
  exact (Set.disjoint_left.mp hs)
    ((mem_resClass_iff ..).mpr ⟨v, rfl⟩)
    ((mem_resClass_iff ..).mpr ⟨u, he⟩)

private def threeDistinct (a b c : Bool × Bool) : Prop := a ≠ b ∧ a ≠ c ∧ b ≠ c

private theorem three_corners :
    ∀ a b c : Bool × Bool, threeDistinct a b c →
      (b = flipFirst a ∧ c = flipSecond a) ∨
      (c = flipFirst a ∧ b = flipSecond a) ∨
      (a = flipFirst b ∧ c = flipSecond b) ∨
      (c = flipFirst b ∧ a = flipSecond b) ∨
      (a = flipFirst c ∧ b = flipSecond c) ∨
      (b = flipFirst c ∧ a = flipSecond c) := by
  unfold threeDistinct flipFirst flipSecond
  decide

private theorem TranspositionPair.no_three (P : TranspositionPair) {c : Bool}
    {a b d : Bool × Bool} {x y z : ℤ} (ha : P.matchesSides c a x) (hb : P.matchesSides c b y)
    (hd : P.matchesSides c d z) (hne : threeDistinct a b d) : False := by
  rcases three_corners a b d hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact P.no_corner ha hb hd
  · exact P.no_corner ha hd hb
  · exact P.no_corner hb ha hd
  · exact P.no_corner hb hd ha
  · exact P.no_corner hd ha hb
  · exact P.no_corner hd hb ha

private def alternating (c : Bool) (i : ℕ) : Bool := if i % 2 = 0 then c else !c

private theorem alternating_add (c : Bool) (i j : ℕ) :
    alternating c (i + j) = alternating (alternating c i) j := by
  by_cases hi : i % 2 = 0 <;> by_cases hj : j % 2 = 0
  · simp [alternating, hi, hj, show (i + j) % 2 = 0 by omega]
  · simp [alternating, hi, hj, show (i + j) % 2 ≠ 0 by omega]
  · simp [alternating, hi, hj, show (i + j) % 2 ≠ 0 by omega]
  · simp [alternating, hi, hj, show (i + j) % 2 = 0 by omega]

private def repeatTwo (a b c d : Bool) : Prop := c = a ∧ d = b

private def oppositeTriples (a b c d e f : Bool) : Prop :=
  c = a ∧ d = !b ∧ e = !a ∧ f = !b

-- The eight entrance sides have 256 assignments. Iskra's forbidden factors correspond to
-- repeated blocks, opposite triples, or three distinct pairs of neighboring classes.
private theorem orientation_cases :
    ∀ a b c d e f g h : Bool,
      repeatTwo a b c d ∨ repeatTwo b c d e ∨ repeatTwo c d e f ∨
      repeatTwo d e f g ∨ repeatTwo e f g h ∨
      (e = a ∧ f = b ∧ g = c ∧ h = d) ∨
      oppositeTriples a b c d e f ∨ oppositeTriples b c d e f g ∨
      oppositeTriples c d e f g h ∨
      threeDistinct (neighborSides a b c) (neighborSides c d e) (neighborSides e f g) ∨
      threeDistinct (neighborSides b c d) (neighborSides d e f) (neighborSides f g h) := by
  unfold repeatTwo oppositeTriples threeDistinct neighborSides
  intro a b c d e f g h
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;>
    cases h <;> decide

private theorem TranspositionPair.joins_reverse (P : TranspositionPair)
    {c s r : Bool} {x y : ℤ} (h : P.joins c s r x y) :
    P.joins (!c) (!r) (!s) y x := by
  unfold joins at *
  simpa only [Bool.not_not] using h.symm

private theorem TranspositionPair.no_eight_step_trace (P : TranspositionPair)
    {n : ℕ} (hn : 0 < n) (hpow : (P.product false) ^ n = 1)
    (c : Bool) (w : ℕ → Bool) (u : ℕ → ℤ)
    (hjoin : ∀ i < 7, P.joins (alternating c i) (w i) (w (i + 1)) (u i) (u (i + 1)))
    (hdistinct : ∀ i j, i < j → j < 8 → alternating c i = alternating c j →
      w i = w j → u i ≠ u j) : False := by
  have join (i j : ℕ) (h : i + j < 7) :
      P.joins (alternating (alternating c i) j) (w (i + j)) (w (i + (j + 1)))
        (u (i + j)) (u (i + (j + 1))) := by
    rw [← alternating_add, ← Nat.add_assoc]
    exact hjoin _ h
  have distinct (i j : ℕ) (hj : 0 < j) (hi : i + j < 8) (heven : j % 2 = 0)
      (hw : w (i + j) = w i) : u i ≠ u (i + j) :=
    hdistinct i (i + j) (by omega) hi (by rw [alternating_add]; simp [alternating, heven]) hw.symm
  have two (i : ℕ) (hi : i < 5)
      (h : repeatTwo (w i) (w (i + 1)) (w (i + 2)) (w (i + 3))) : False := by
    obtain ⟨h₁, h₂⟩ := h
    apply P.no_repeat_two hn (P.product_pow_eq_one hpow (alternating c i))
      (by simpa [alternating] using join i 0 (by omega))
      (by simpa [alternating, h₁] using join i 1 (by omega))
      (by simpa [alternating, h₁, h₂] using join i 2 (by omega))
      (distinct i 2 (by decide) (by omega) (by decide) h₁)
  have four (e : w 4 = w 0) (f : w 5 = w 1) (g : w 6 = w 2) (h : w 7 = w 3) : False := by
    apply P.no_repeat_four hn (P.product_pow_eq_one hpow c)
      (by simpa [alternating] using hjoin 0 (by decide))
      (by simpa [alternating] using hjoin 1 (by decide))
      (by simpa [alternating] using hjoin 2 (by decide))
      (by simpa [alternating, e] using hjoin 3 (by decide))
      (by simpa [alternating, e, f] using hjoin 4 (by decide))
      (by simpa [alternating, f, g] using hjoin 5 (by decide))
      (by simpa [alternating, g, h] using hjoin 6 (by decide))
      (distinct 0 4 (by decide) (by decide) (by decide) e)
  have opposite (i : ℕ) (hi : i < 3)
      (h : oppositeTriples (w i) (w (i + 1)) (w (i + 2)) (w (i + 3))
        (w (i + 4)) (w (i + 5))) : False := by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    have hlast := P.joins_reverse (join i 4 (by omega))
    have hprev := P.joins_reverse (join i 3 (by omega))
    exact P.no_opposite_triples hn (P.product_pow_eq_one hpow (alternating c i))
      (by simpa [alternating] using join i 0 (by omega))
      (by simpa [alternating, h₁] using join i 1 (by omega))
      (by simpa [alternating, h₃, h₄] using hlast)
      (by simpa [alternating, h₂, h₃] using hprev)
      (distinct i 2 (by decide) (by omega) (by decide) h₁)
  have three (i : ℕ) (hi : i < 2)
      (h : threeDistinct (neighborSides (w i) (w (i + 1)) (w (i + 2)))
        (neighborSides (w (i + 2)) (w (i + 3)) (w (i + 4)))
        (neighborSides (w (i + 4)) (w (i + 5)) (w (i + 6)))) : False := by
    have matched (j : ℕ) (hj : j % 2 = 0) (hj' : i + j + 1 < 7) :
        P.matchesSides (!(alternating c i))
          (neighborSides (w (i + j)) (w (i + (j + 1))) (w (i + (j + 2))))
          (u (i + (j + 1))) := by
      have hodd : (j + 1) % 2 ≠ 0 := by omega
      apply P.matches_of_joins
        (by simpa [alternating, hj] using join i j (by omega))
        (by simpa [alternating, hodd, Nat.add_assoc] using join i (j + 1) (by omega))
    exact P.no_three
      (by simpa using matched 0 (by decide) (by omega))
      (by simpa using matched 2 (by decide) (by omega))
      (by simpa using matched 4 (by decide) (by omega)) h
  rcases orientation_cases (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) with
    h | h | h | h | h | ⟨e, f, g, h⟩ | h | h | h | h | h
  · exact two 0 (by decide) h
  · exact two 1 (by decide) h
  · exact two 2 (by decide) h
  · exact two 3 (by decide) h
  · exact two 4 (by decide) h
  · exact four e f g h
  · exact opposite 0 (by decide) h
  · exact opposite 1 (by decide) h
  · exact opposite 2 (by decide) h
  · exact three 0 (by decide) h
  · exact three 1 (by decide) h

private def TranspositionPair.graph (P : TranspositionPair) : SimpleGraph ℤ where
  Adj x y := x ≠ y ∧ ∃ c, P.perm c x = y
  symm := ⟨by
    rintro x y ⟨hne, c, rfl⟩
    exact ⟨hne.symm, c, P.involutive c x⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem TranspositionPair.alternating_path (P : TranspositionPair)
    {x y : ℤ} {p : P.graph.Walk x y} (hp : p.IsPath) :
    ∃ c : Bool, ∀ i < p.length, P.perm (alternating c i) (p.getVert i) = p.getVert (i + 1) := by
  classical
  have edge (i : ℕ) (hi : i < p.length) : ∃ c, P.perm c (p.getVert i) = p.getVert (i + 1) :=
    (p.adj_getVert_succ hi).2
  let color (i : ℕ) := if h : i < p.length then (edge i h).choose else false
  have hcolor (i : ℕ) (hi : i < p.length) :
      P.perm (color i) (p.getVert i) = p.getVert (i + 1) := by
    simpa only [color, dite_eq_left hi] using (edge i hi).choose_spec
  have hnext (i : ℕ) (hi : i + 1 < p.length) : color (i + 1) = !(color i) := by
    have hne : color (i + 1) ≠ color i := by
      intro he
      have h₁ := hcolor i (by omega)
      have h₂ := hcolor (i + 1) hi
      rw [he, ← h₁, P.involutive] at h₂
      have := hp.getVert_injOn (show i ≤ p.length by omega)
        (show i + 1 + 1 ≤ p.length by omega) h₂
      omega
    cases h : color i <;> cases h' : color (i + 1) <;> simp_all
  have he (i : ℕ) (hi : i < p.length) : color i = alternating (color 0) i := by
    induction i with
    | zero => simp [alternating]
    | succ i ih =>
      rw [hnext i hi, ih (by omega), alternating_add]
      simp [alternating]
  exact ⟨color 0, fun i hi => he i hi ▸ hcolor i hi⟩

private theorem TranspositionPair.path_length_lt_eight (P : TranspositionPair) {n : ℕ}
    (hn : 0 < n) (hpow : (P.product false) ^ n = 1)
    {x y : ℤ} {p : P.graph.Walk x y} (hp : p.IsPath) : p.length < 8 := by
  classical
  by_contra! hlong
  obtain ⟨c, hc⟩ := P.alternating_path hp
  have moved (i : ℕ) (hi : i < 8) : P.perm (alternating c i) (p.getVert i) ≠ p.getVert i := by
    rw [hc i (by omega)]
    exact (p.adj_getVert_succ (by omega : i < p.length)).ne.symm
  have label (i : ℕ) (hi : i < 8) :
      ∃ s k, p.getVert i = P.point (alternating c i) s k := P.exists_point (moved i hi)
  let w (i : ℕ) := if hi : i < 8 then (label i hi).choose else false
  let u (i : ℕ) := if hi : i < 8 then (label i hi).choose_spec.choose else 0
  have hpoint (i : ℕ) (hi : i < 8) :
      p.getVert i = P.point (alternating c i) (w i) (u i) := by
    simpa only [w, u, dite_eq_left hi] using (label i hi).choose_spec.choose_spec
  apply P.no_eight_step_trace hn hpow c w u
  · intro i hi
    have hstep := hc i (by omega)
    rw [hpoint i (by omega), hpoint (i + 1) (by omega), P.apply_point,
      alternating_add c i 1] at hstep
    exact hstep
  · intro i j hij hj hcolor hside he
    have hp₁ := hpoint i (by omega)
    have hp₂ := hpoint j hj
    rw [hcolor, hside, he, ← hp₂] at hp₁
    have := hp.getVert_injOn (show i ≤ p.length by omega) (show j ≤ p.length by omega) hp₁
    omega

private def TranspositionPair.follow (P : TranspositionPair) (c : Bool) (x : ℤ) : ℕ → ℤ
  | 0 => x
  | i + 1 => P.perm (alternating c i) (P.follow c x i)

private def TranspositionPair.endpoints (P : TranspositionPair) (x : ℤ) : Finset ℤ :=
  Finset.univ.image (fun p : Bool × Fin 8 => P.follow p.1 x p.2)

private theorem TranspositionPair.card_endpoints (P : TranspositionPair) (x : ℤ) :
    (P.endpoints x).card ≤ 16 := by
  exact Finset.card_image_le.trans (by simp)

private theorem TranspositionPair.mem_endpoints (P : TranspositionPair)
    {n : ℕ} (hn : 0 < n) (hpow : (P.product false) ^ n = 1)
    {x y : ℤ} (hxy : P.graph.Reachable x y) : y ∈ P.endpoints x := by
  obtain ⟨p, hp⟩ := hxy.exists_isPath
  obtain ⟨c, hc⟩ := P.alternating_path hp
  have hfollow (i : ℕ) (hi : i ≤ p.length) : P.follow c x i = p.getVert i := by
    induction i with
    | zero => simp [follow]
    | succ i ih => rw [follow, ih (by omega), hc i (by omega)]
  exact Finset.mem_image.mpr ⟨(c, ⟨p.length, P.path_length_lt_eight hn hpow hp⟩),
    Finset.mem_univ _, (hfollow _ le_rfl).trans p.getVert_length⟩

private theorem TranspositionPair.reachable_perm (P : TranspositionPair) (c : Bool) (x : ℤ) :
    P.graph.Reachable x (P.perm c x) := by
  by_cases h : x = P.perm c x
  · rw [← h]
  · exact (show P.graph.Adj x (P.perm c x) from ⟨h, c, rfl⟩).reachable

private theorem TranspositionPair.reachable_iterate (P : TranspositionPair) (x : ℤ) (i : ℕ) :
    P.graph.Reachable x ((P.product false : ℤ → ℤ)^[i] x) := by
  induction i with
  | zero => exact .rfl
  | succ i ih =>
    rw [iterate_succ_apply']
    exact ih.trans ((P.reachable_perm false _).trans (P.reachable_perm true _))

private theorem TranspositionPair.order_dvd_factorial (P : TranspositionPair)
    {n : ℕ} (hn : 0 < n) (hpow : (P.product false) ^ n = 1) :
    orderOf (P.product false) ∣ (16 : ℕ).factorial := by
  apply orderOf_dvd_of_pow_eq_one
  ext x
  let f : ℤ → ℤ := P.product false
  have hperiodic : IsPeriodicPt f n x := by
    change f^[n] x = x
    rw [Equiv.Perm.iterate_eq_pow]
    exact DFunLike.congr_fun hpow x
  have hpos := minimalPeriod_pos_of_mem_periodicPts (mk_mem_periodicPts hn hperiodic)
  have hsize : minimalPeriod f x ≤ (P.endpoints x).card := by
    simpa using Finset.card_le_card_of_injOn (s := Finset.range (minimalPeriod f x))
      (t := P.endpoints x) (fun i => f^[i] x)
      (fun i _ => P.mem_endpoints hn hpow (P.reachable_iterate x i))
      (fun _ hi _ hj he => iterate_injOn_Iio_minimalPeriod
        (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) he)
  have h := isPeriodicPt_iff_minimalPeriod_dvd.mpr
    (Nat.dvd_factorial hpos (hsize.trans (P.card_endpoints x)))
  change (P.product false ^ (16 : ℕ).factorial) x = x
  simpa only [IsPeriodicPt, IsFixedPt, f, Equiv.Perm.iterate_eq_pow] using h

/--
**Products of two class transpositions have only finitely many orders.** The claim of Kourovka
Problem 18.48 holds: the set of positive integers $k$ such that $\sigma\tau$ has order $k$ for some
class transpositions $\sigma$ and $\tau$ of $\mathbb{Z}$ is finite.

Iskra (2026), accepted in the Kourovka Notebook (21st issue), proves that every finite order of a
product of two class transpositions divides $840$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.48 (S. Kohl); resolution: A. Iskra,
Finite orders of products of two class transpositions divide 840, preprint, arXiv:2610.01793
(2026), abstract: if the product of two class transpositions has finite order, then its order
divides 840 (sharp); this answers Question 18.48 affirmatively, as the Kourovka Notebook (21st
issue) records, https://arxiv.org/abs/2610.01793.
-/
theorem classTranspositionProductOrdersFinite_holds :
    classTranspositionProductOrdersFinite := by
  apply (Set.finite_Icc 1 (16 : ℕ).factorial).subset
  rintro n ⟨hn, σ, τ, ⟨r₁, m₁, r₂, m₂, hσ⟩, ⟨r₃, m₃, r₄, m₄, hτ⟩, horder⟩
  let P : TranspositionPair :=
    ⟨fun c => if c then σ else τ,
      fun c s => if c then (if s then r₂ else r₁) else (if s then r₄ else r₃),
      fun c s => if c then (if s then m₂ else m₁) else (if s then m₄ else m₃),
      fun c => by cases c <;> assumption⟩
  have hpow : (P.product false) ^ n = 1 := by
    change (σ * τ) ^ n = 1
    rw [← horder, pow_orderOf_eq_one]
  have hdvd := P.order_dvd_factorial hn hpow
  change orderOf (σ * τ) ∣ (16 : ℕ).factorial at hdvd
  rw [horder] at hdvd
  exact ⟨hn, Nat.le_of_dvd (Nat.factorial_pos _) hdvd⟩

end MathlibExt.GroupTheory.ClassTranspositionProductOrdersKourovka18Problem48Wanted
