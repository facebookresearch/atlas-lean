/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeInterval.Breusch.Grid
public import MathlibExt.NumberTheory.PrimeInterval.Breusch.Lower
import MathlibExt.NumberTheory.PrimeInterval.Breusch.Theta
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Primorial
import Mathlib.Computability.Reduce
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Breusch upper bound via the continuous `G`-function

The continuous `G9r` function, its identification with the grid `G9`, the `p`-adic
valuation identity for the weighted product, and the resulting upper bound
`logF9_upper` under the assumption that `(1890 * n, 2100 * n]` holds no prime.
-/

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

open Nat Finset

/-- **Continuous Breusch function.** For real $x$, the continuous Breusch function is the
integer

$$G(x) = \sum_{d \mid 210} \mu(d) \left( \lfloor 2100x/d \rfloor - \lfloor 1890x/d \rfloor -
\lfloor 210x/d \rfloor \right),$$

where $d$ ranges over the positive divisors of $210$, $\mu$ is the Möbius function, and each
floor is the natural-number floor, which is $0$ for negative arguments. -/
noncomputable def G9r (x : ℝ) : ℤ := w9.toFinset.sum (fun q : ℕ × ℤ =>
  q.2 * ((Int.ofNat ⌊((10*Q9:ℕ):ℝ)*x/(q.1:ℝ)⌋₊)
    - (Int.ofNat ⌊((9*Q9:ℕ):ℝ)*x/(q.1:ℝ)⌋₊) - (Int.ofNat ⌊((Q9:ℕ):ℝ)*x/(q.1:ℝ)⌋₊)))

/-- **Floor of a quotient of natural numbers.** For all natural numbers $a$ and $b$, the floor of
the real number $a / b$ equals the quotient of $a$ by $b$ in integer division. When $b = 0$ both
sides are $0$, since division by zero gives $0$ in both the reals and the natural numbers. -/
lemma nat_floor_nat_div (a b : ℕ) : ⌊((a:ℝ))/((b:ℝ))⌋₊ = a / b := by
  by_cases hb : b = 0
  · subst hb; simp
  · have hb0 : (0:ℝ) < (b:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hb)
    rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ (a:ℝ)/(b:ℝ))]
    constructor
    · rw [le_div_iff₀ hb0]
      have h := Nat.div_mul_le_self a b
      have hc : ((((a/b)*b : ℕ)):ℝ) ≤ (a:ℝ) := by exact_mod_cast h
      push_cast at hc
      linarith [hc]
    · rw [div_lt_iff₀ hb0]
      have hmod : a % b < b := Nat.mod_lt a (by omega)
      have hdm : b*(a/b) + a%b = a := Nat.div_add_mod a b
      have hc : (((b*(a/b) + a%b : ℕ)):ℝ) = (a:ℝ) := by exact_mod_cast hdm
      have hmodR : ((a%b : ℕ):ℝ) < (b:ℝ) := by exact_mod_cast hmod
      push_cast at hc ⊢
      linarith [hc, hmodR]

/-- **Remainder bound for common multiples.** Let $a$, $b$, $d$ be natural numbers with $b > 0$,
$d > 0$, $d \mid b$ and $d \mid a$. Then the remainder of $a$ modulo $b$ is at most $b - d$. -/
lemma nat_mod_le_of_dvd (a b d : ℕ) (hb : 0 < b) (_hd0 : 0 < d)
    (hdb : d ∣ b) (hda : d ∣ a) : a % b ≤ b - d := by
  have hdvdmod : d ∣ a % b := (Nat.dvd_mod_iff hdb).mpr hda
  by_contra hlt
  have hlt' : b - d < a % b := lt_of_not_ge hlt
  have hmod0 : a % b < b := Nat.mod_lt a hb
  have hsub : d ∣ b - a % b := Nat.dvd_sub hdb hdvdmod
  have hmod : a % b < b := Nat.mod_lt a hb
  have hpos : 0 < b - a % b := by omega
  have hlt2 : b - a % b < d := by omega
  have hle := Nat.le_of_dvd hpos hsub
  omega

/-- **Real floors at divisors of 210 agree with grid floors.** Let $C$ and $L$ be positive natural
numbers, let $m$ be a divisor of $210$ with $C \mid mL$, and let $x \ge 0$ be a real number. Then
$\lfloor Cx/m \rfloor = \lfloor C \lfloor Lx \rfloor / (mL) \rfloor$. -/
lemma floor_grid_match (C L : ℕ) (hC : 0 < C) (hL : 0 < L) (m : ℕ) (hm : m ∣ 210)
    (hCmL : C ∣ m * L) (x : ℝ) (hx : 0 ≤ x) :
    ⌊((C:ℕ):ℝ)*x/(m:ℝ)⌋₊ = C*⌊((L:ℕ):ℝ)*x⌋₊/(m*L) := by
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm (by norm_num)
  have hmL0 : 0 < m*L := Nat.mul_pos hm0 hL
  have hm0R : (m:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm0)
  have hL0R : (L:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  have hmL0R : ((m*L:ℕ):ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hmL0)
  have hfl : (((⌊((L:ℕ):ℝ)*x⌋₊ : ℕ)):ℝ) ≤ (L:ℝ)*x := Nat.floor_le (by positivity)
  have hlt : (L:ℝ)*x < (((⌊((L:ℕ):ℝ)*x⌋₊ : ℕ)):ℝ)+1 := Nat.lt_floor_add_one _
  set s : ℝ := (L:ℝ)*x - ⌊((L:ℕ):ℝ)*x⌋₊ with hs
  have hs0 : 0 ≤ s := by linarith [hfl]
  have hs1 : s < 1 := by linarith [hlt]
  have hCj : C*⌊((L:ℕ):ℝ)*x⌋₊
      = (m*L)*(C*⌊((L:ℕ):ℝ)*x⌋₊/(m*L)) + C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) :=
    (Nat.div_add_mod _ _).symm
  have hmod_le : C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) ≤ m*L - C :=
    nat_mod_le_of_dvd _ _ _ hmL0 hC hCmL (Nat.dvd_mul_right C _)
  have hCmL' : C ≤ m*L := Nat.le_of_dvd hmL0 hCmL
  have hfrac_lt : ((C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) : ℕ):ℝ) + (C:ℝ)*s < ((m*L : ℕ):ℝ) := by
    have h1 : ((C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) : ℕ):ℝ) ≤ ((m*L - C : ℕ):ℝ) := by
      exact_mod_cast hmod_le
    rw [Nat.cast_sub hCmL'] at h1
    have hC0 : (0:ℝ) < C := by exact_mod_cast hC
    have hsC : (C:ℝ)*s < (C:ℝ) := by
      have h := mul_lt_mul_of_pos_left hs1 hC0
      simpa using h
    linarith [h1, hsC]
  have hxeq : x = ((((⌊((L:ℕ):ℝ)*x⌋₊ : ℕ):ℝ) + s)) / (L:ℝ) := by
    rw [hs]
    field_simp
    ring
  have e1 : ((C:ℕ):ℝ)*x/(m:ℝ)
      = ((((C*⌊((L:ℕ):ℝ)*x⌋₊ : ℕ):ℝ) + (C:ℝ)*s)) / ((m*L : ℕ):ℝ) := by
    conv_lhs => rw [hxeq]
    push_cast
    field_simp
  have e2 : ((((C*⌊((L:ℕ):ℝ)*x⌋₊ : ℕ):ℝ) + (C:ℝ)*s)) / ((m*L : ℕ):ℝ)
      = (((C*⌊((L:ℕ):ℝ)*x⌋₊/(m*L) : ℕ)):ℝ)
        + ((((C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) : ℕ)):ℝ) + (C:ℝ)*s) / ((m*L : ℕ):ℝ) := by
    have hCjR : ((C*⌊((L:ℕ):ℝ)*x⌋₊ : ℕ):ℝ)
        = ((m*L : ℕ):ℝ) * (((C*⌊((L:ℕ):ℝ)*x⌋₊/(m*L) : ℕ)):ℝ)
          + ((C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) : ℕ):ℝ) := by exact_mod_cast hCj
    field_simp
    linarith [hCjR]
  rw [e1, e2, Nat.floor_eq_iff (by positivity :
    (0:ℝ) ≤ (((C*⌊((L:ℕ):ℝ)*x⌋₊/(m*L) : ℕ)):ℝ)
      + ((((C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) : ℕ)):ℝ) + (C:ℝ)*s) / ((m*L : ℕ):ℝ))]
  constructor
  · -- N ≤ N + frac
    have hnn : (0:ℝ) ≤ ((((C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) : ℕ)):ℝ) + (C:ℝ)*s)
        / ((m*L : ℕ):ℝ) := by positivity
    linarith [hnn]
  · -- N + frac < N + 1
    have hlt1 : ((((C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) : ℕ)):ℝ) + (C:ℝ)*s)
        / ((m*L : ℕ):ℝ) < 1 := by
      rw [div_lt_one (by exact_mod_cast hmL0 : (0:ℝ) < ((m*L:ℕ):ℝ))]
      linarith [hfrac_lt]
    linarith [hlt1]

-- One-period shift of a single div term. Needs m ∣ C (true for C ∈ {2100,1890,210}
-- when m ∣ 210, since 210 ∣ C).
/-- **Shifting a floor quotient by one period.** Let $C$ and $m$ be natural numbers with $m > 0$
and $m \mid C$. Then for every natural number $j$,
$\lfloor C(j + 18900)/(18900m) \rfloor = \lfloor Cj/(18900m) \rfloor + C/m$. -/
lemma div_shift189 (C m : ℕ) (hmC : m ∣ C) (hm0 : 0 < m) (j : ℕ) :
    (C*(j+18900))/(m*18900) = C*j/(m*18900) + C/m := by
  have hdm : C/m*m = C := Nat.div_mul_cancel hmC
  have hC : C*(j+18900) = C*j + (C/m)*(m*18900) := by
    have hK : (C/m)*(m*18900) = C*18900 := by
      calc (C/m)*(m*18900) = (C/m*m)*18900 := by ring
        _ = C*18900 := by rw [hdm]
    rw [hK]; ring
  rw [hC, Nat.add_mul_div_right _ _ (Nat.mul_pos hm0 (by norm_num))]

-- G9 is 18900-periodic: each C/m shift is integral and 10-9-1 cancels.
/-- **One-period shift of $G_9$.** For every natural number $j$, the grid $G$-function for $k = 9$
satisfies $G_9(j + 18900) = G_9(j)$. -/
lemma G9_shift (j : ℕ) : G9 (j + 18900) = G9 j := by
  have hterm : ∀ q ∈ w9.toFinset, G9term q (j+18900) = G9term q j := by
    intro q hq
    have hqmem : q ∈ w9 := List.mem_toFinset.mp hq
    have hm : q.1 ∣ 210 := by rw [← Q9_eq]; exact w9_dvd q hqmem
    have hm0 : 0 < q.1 := w9_pos q hqmem
    have ⟨t, ht⟩ := hm
    have h210 : 210/q.1 = t := by rw [ht]; exact Nat.mul_div_cancel_left _ hm0
    have h9 : 9*210/q.1 = 9*t := by
      rw [ht, show 9*(q.1*t) = q.1*(9*t) by ring]
      exact Nat.mul_div_cancel_left _ hm0
    have h10 : 10*210/q.1 = 10*t := by
      rw [ht, show 10*(q.1*t) = q.1*(10*t) by ring]
      exact Nat.mul_div_cancel_left _ hm0
    have hK : ((10*210/q.1 : ℕ):ℤ) = ((9*210/q.1 : ℕ):ℤ) + ((210/q.1 : ℕ):ℤ) := by
      rw [h10, h9, h210]; push_cast; ring
    have e10 := div_shift189 (10*210) q.1 (dvd_trans hm (Nat.dvd_mul_left 210 10)) hm0 j
    have e9 := div_shift189 (9*210) q.1 (dvd_trans hm (Nat.dvd_mul_left 210 9)) hm0 j
    have e1 := div_shift189 210 q.1 hm hm0 j
    unfold G9term
    rw [e10, e9, e1]
    simp only [Nat.cast_add]
    linear_combination q.2 * hK
  have e1 := map_sum_toFinset w9 w9_nodup (fun q => G9term q (j+18900))
  have e2 := map_sum_toFinset w9 w9_nodup (fun q => G9term q j)
  unfold G9
  rw [e1, e2]
  exact Finset.sum_congr rfl hterm

/-- **Periodicity of $G_9$ in multiples of $18900$.** For all natural numbers $o$ and $r$, the
grid $G$-function for $k = 9$ satisfies $G_9(18900\,o + r) = G_9(r)$. -/
lemma G9_period_iter (o r : ℕ) : G9 (18900*o + r) = G9 r := by
  induction o with
  | zero => simp
  | succ o ih =>
    rw [show 18900*(o+1)+r = (18900*o+r)+18900 by ring, G9_shift, ih]

/-- **$G_9$ depends only on the residue modulo $18900$.** For every natural number $j$, the grid
$G$-function for $k = 9$ satisfies $G_9(j) = G_9(j \bmod 18900)$. -/
lemma G9_eq_mod (j : ℕ) : G9 j = G9 (j % 18900) := by
  conv_lhs => rw [← Nat.div_add_mod j 18900]
  exact G9_period_iter _ _

-- Continuous-to-grid identity via floor_grid_match (L = 18900).
/-- **The continuous Breusch function agrees with the grid function.** For every real
$x \ge 0$, the continuous Breusch function $G$ and the Breusch grid function $G_9$ satisfy
$G(x) = G_9(\lfloor 18900x \rfloor)$. -/
lemma G9r_eq_grid (x : ℝ) (hx : 0 ≤ x) : G9r x = G9 ⌊(18900:ℝ)*x⌋₊ := by
  have hterm : ∀ q ∈ w9.toFinset,
      q.2 * ((Int.ofNat ⌊((10*Q9:ℕ):ℝ)*x/(q.1:ℝ)⌋₊)
        - (Int.ofNat ⌊((9*Q9:ℕ):ℝ)*x/(q.1:ℝ)⌋₊)
        - (Int.ofNat ⌊((Q9:ℕ):ℝ)*x/(q.1:ℝ)⌋₊))
      = G9term q ⌊(18900:ℝ)*x⌋₊ := by
    intro q hq
    have hqmem : q ∈ w9 := List.mem_toFinset.mp hq
    have hm : q.1 ∣ 210 := by rw [← Q9_eq]; exact w9_dvd q hqmem
    have e10 := floor_grid_match (10*Q9) 18900 (by rw [Q9_eq]; norm_num) (by norm_num)
      q.1 hm ⟨q.1*9, by rw [Q9_eq]; ring⟩ x hx
    have e9 := floor_grid_match (9*Q9) 18900 (by rw [Q9_eq]; norm_num) (by norm_num)
      q.1 hm ⟨q.1*10, by rw [Q9_eq]; ring⟩ x hx
    have e1 := floor_grid_match Q9 18900 (by rw [Q9_eq]; norm_num) (by norm_num)
      q.1 hm ⟨q.1*90, by rw [Q9_eq]; ring⟩ x hx
    rw [e10, e9, e1]
    unfold G9term
    simp only [Int.ofNat_eq_natCast, Q9_eq, Nat.cast_ofNat]
  unfold G9r G9
  rw [map_sum_toFinset w9 w9_nodup (fun q => G9term q ⌊(18900:ℝ)*x⌋₊)]
  exact Finset.sum_congr rfl hterm

-- Small-grid certificates.
/-- **The Breusch grid function vanishes below 9.** For every natural number $j < 9$, the
Breusch grid function $G_9$ satisfies $G_9(j) = 0$. -/
theorem G9_zero9 : ∀ j < 9, G9 j = 0 := by decide
/-- **Value of $G_9$ at $9$.** The grid $G$-function for $k = 9$ satisfies $G_9(9) = 1$. -/
theorem G9_at9 : G9 9 = 1 := by decide
/-- **Bound $G_9 \le 1$ below $10$.** For every natural number $j < 10$, the grid $G$-function for
$k = 9$ satisfies $G_9(j) \le 1$. -/
theorem G9_small_le1 : ∀ j < 10, G9 j ≤ 1 := by decide

-- Consequences of the grid certificate for the continuous function.
/-- **The continuous Breusch function is at most 3.** For every real $x \ge 0$, the continuous
Breusch function $G$ satisfies $G(x) \le 3$. -/
theorem G9r_le3 (x : ℝ) (hx : 0 ≤ x) : G9r x ≤ 3 := by
  rw [G9r_eq_grid x hx, G9_eq_mod]
  exact M9_le _ (Nat.mod_lt _ (by norm_num))

/-- **The continuous Breusch function vanishes near zero.** For every real $x$ with
$0 \le x < 1/2100$, the continuous Breusch function $G$ satisfies $G(x) = 0$. -/
theorem G9r_vanish (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 1 / ((10 * Q9 : ℕ) : ℝ)) :
    G9r x = 0 := by
  have h10 : ((10 * Q9 : ℕ) : ℝ) = 2100 := by rw [Q9_eq]; norm_num
  rw [h10] at hx
  rw [G9r_eq_grid x hx0]
  have hj : ⌊(18900 : ℝ) * x⌋₊ < 9 := by
    rw [Nat.floor_lt (mul_nonneg (by norm_num) hx0)]
    push_cast
    linarith
  exact G9_zero9 _ hj

/-- **Level-$1$ threshold for the continuous Breusch function.** Let $Q_9 = 210$. For every real
$x \ge 1/(9 Q_9) = 1/1890$, if the continuous Breusch function $G$ satisfies $G(x) \ge 1$, then
$x \ge 279/18900$. -/
theorem G9r_level1 (x : ℝ) (hx : 1 / ((9 * Q9 : ℕ) : ℝ) ≤ x) (h : 1 ≤ G9r x) :
    (279 : ℝ) / 18900 ≤ x := by
  have h9 : ((9 * Q9 : ℕ) : ℝ) = 1890 := by rw [Q9_eq]; norm_num
  rw [h9] at hx
  have hx0 : 0 ≤ x := by linarith
  rw [G9r_eq_grid x hx0, G9_eq_mod] at h
  set r := ⌊(18900 : ℝ) * x⌋₊ % 18900 with hr
  have hj10 : 10 ≤ ⌊(18900 : ℝ) * x⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith
  have hdecomp := Nat.div_add_mod ⌊(18900 : ℝ) * x⌋₊ 18900
  -- Either r ≥ 10 (jmin route) or r = 9 with quotient ≥ 1 (j ≥ 18909).
  have key : 279 ≤ ⌊(18900 : ℝ) * x⌋₊ := by
    by_cases hr10 : 10 ≤ r
    · have h279 : 279 ≤ r := by
        by_contra hc
        push Not at hc
        have hlt := jmin1.2 r hr10 hc
        omega
      have hmod : r ≤ ⌊(18900 : ℝ) * x⌋₊ := Nat.mod_le _ _
      omega
    · push Not at hr10
      have hr9 : r = 9 := by
        by_contra hc
        have hr9' : r < 9 := by omega
        have hz := G9_zero9 r hr9'
        omega
      omega
  have hfloor : ((⌊(18900 : ℝ) * x⌋₊ : ℕ):ℝ) ≤ (18900 : ℝ) * x :=
    Nat.floor_le (mul_nonneg (by norm_num) hx0)
  have hkeyR : (279 : ℝ) ≤ ((⌊(18900 : ℝ) * x⌋₊ : ℕ):ℝ) := by exact_mod_cast key
  linarith

/-- **Level-$2$ threshold for the continuous Breusch function.** Let $Q_9 = 210$. For every real
$x \ge 1/(9 Q_9) = 1/1890$, if the continuous Breusch function $G$ satisfies $G(x) \ge 2$, then
$x \ge 657/18900$. -/
theorem G9r_level2 (x : ℝ) (hx : 1 / ((9 * Q9 : ℕ) : ℝ) ≤ x) (h : 2 ≤ G9r x) :
    (657 : ℝ) / 18900 ≤ x := by
  have h9 : ((9 * Q9 : ℕ) : ℝ) = 1890 := by rw [Q9_eq]; norm_num
  rw [h9] at hx
  have hx0 : 0 ≤ x := by linarith
  rw [G9r_eq_grid x hx0, G9_eq_mod] at h
  set r := ⌊(18900 : ℝ) * x⌋₊ % 18900 with hr
  have key : 657 ≤ ⌊(18900 : ℝ) * x⌋₊ := by
    by_cases hr10 : 10 ≤ r
    · have h657 : 657 ≤ r := by
        by_contra hc
        push Not at hc
        have hlt := jmin2.2 r hr10 hc
        omega
      have hmod : r ≤ ⌊(18900 : ℝ) * x⌋₊ := Nat.mod_le _ _
      omega
    · push Not at hr10
      have hle := G9_small_le1 r hr10
      omega
  have hfloor : ((⌊(18900 : ℝ) * x⌋₊ : ℕ):ℝ) ≤ (18900 : ℝ) * x :=
    Nat.floor_le (mul_nonneg (by norm_num) hx0)
  have hkeyR : (657 : ℝ) ≤ ((⌊(18900 : ℝ) * x⌋₊ : ℕ):ℝ) := by exact_mod_cast key
  linarith

/-- **Level-$3$ threshold for the continuous Breusch function.** Let $Q_9 = 210$. For every real
$x \ge 1/(9 Q_9) = 1/1890$, if the continuous Breusch function $G$ satisfies $G(x) \ge 3$, then
$x \ge 963/18900$. -/
theorem G9r_level3 (x : ℝ) (hx : 1 / ((9 * Q9 : ℕ) : ℝ) ≤ x) (h : 3 ≤ G9r x) :
    (963 : ℝ) / 18900 ≤ x := by
  have h9 : ((9 * Q9 : ℕ) : ℝ) = 1890 := by rw [Q9_eq]; norm_num
  rw [h9] at hx
  have hx0 : 0 ≤ x := by linarith
  rw [G9r_eq_grid x hx0, G9_eq_mod] at h
  set r := ⌊(18900 : ℝ) * x⌋₊ % 18900 with hr
  have key : 963 ≤ ⌊(18900 : ℝ) * x⌋₊ := by
    by_cases hr10 : 10 ≤ r
    · have h963 : 963 ≤ r := by
        by_contra hc
        push Not at hc
        have hlt := jmin3.2 r hr10 hc
        omega
      have hmod : r ≤ ⌊(18900 : ℝ) * x⌋₊ := Nat.mod_le _ _
      omega
    · push Not at hr10
      have hle := G9_small_le1 r hr10
      omega
  have hfloor : ((⌊(18900 : ℝ) * x⌋₊ : ℕ):ℝ) ≤ (18900 : ℝ) * x :=
    Nat.floor_le (mul_nonneg (by norm_num) hx0)
  have hkeyR : (963 : ℝ) ≤ ((⌊(18900 : ℝ) * x⌋₊ : ℕ):ℝ) := by exact_mod_cast key
  linarith

/-- **Integer cast of the floor of a quotient of natural numbers.** For natural numbers $t$ and
$d$, the floor of the real number $t/d$, as an integer, equals the natural-number quotient of $t$
by $d$ (rounded down), as an integer. Both sides are $0$ when $d = 0$, since division by zero is
$0$ for both real numbers and natural numbers. -/
lemma intFloor_cast (t d : ℕ) :
    (Int.ofNat ⌊((t : ℕ) : ℝ) / ((d : ℕ) : ℝ)⌋₊ : ℤ) = ((t / d : ℕ) : ℤ) := by
  rw [nat_floor_nat_div]
  exact Int.ofNat_eq_natCast _

-- Nat divs in Legendre sums equal the G9r floors.
/-- **Legendre terms of $N_{10}$ as real floors.** Let $m \ge 1$ divide $Q_9 = 210$, and let
$p \ge 2$, $n$ and $j$ be natural numbers. Write $N_{10}(m, n) = 10n \cdot (Q_9/m)$.
Then $\lfloor N_{10}(m, n)/p^j \rfloor$ equals the floor of the real number $10 Q_9 (n/p^j)/m$. -/
lemma floor_N10 {m n p j : ℕ} (hm : 1 ≤ m) (hd : m ∣ Q9) (hp2 : 2 ≤ p) :
    ((N10m m n / p ^ j : ℕ) : ℤ)
      = Int.ofNat ⌊((10*Q9:ℕ):ℝ)*((n : ℝ) / (((p ^ j : ℕ)) : ℝ))/((m : ℕ) : ℝ)⌋₊ := by
  have hp0 : p ≠ 0 := by omega
  have hmp : m * p ^ j ≠ 0 := mul_ne_zero (by omega) (pow_ne_zero j hp0)
  have hmR : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hpjR : ((((p ^ j : ℕ))) : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero j hp0)
  have hdiv : N10m m n / p ^ j = 10 * Q9 * n / (m * p ^ j) := by
    rw [N10_eq hm hd, Nat.div_div_eq_div_mul]
  rw [hdiv]
  have he : ((10*Q9:ℕ):ℝ)*((n : ℝ) / (((p ^ j : ℕ)) : ℝ))/((m : ℕ) : ℝ)
      = (((10 * Q9 * n : ℕ)) : ℝ) / (((m * p ^ j : ℕ)) : ℝ) := by
    push_cast
    field_simp
  rw [he]
  exact (intFloor_cast _ _).symm

/-- **Legendre terms of $N_9$ as real floors.** Let $m \ge 1$ divide $Q_9 = 210$, and let
$p \ge 2$, $n$ and $j$ be natural numbers. Write $N_9(m, n) = 9n \cdot (Q_9/m)$.
Then $\lfloor N_9(m, n)/p^j \rfloor$ equals the floor of the real number $9 Q_9 (n/p^j)/m$. -/
lemma floor_N9 {m n p j : ℕ} (hm : 1 ≤ m) (hd : m ∣ Q9) (hp2 : 2 ≤ p) :
    ((N9m m n / p ^ j : ℕ) : ℤ)
      = Int.ofNat ⌊((9*Q9:ℕ):ℝ)*((n : ℝ) / (((p ^ j : ℕ)) : ℝ))/((m : ℕ) : ℝ)⌋₊ := by
  have hp0 : p ≠ 0 := by omega
  have hmp : m * p ^ j ≠ 0 := mul_ne_zero (by omega) (pow_ne_zero j hp0)
  have hmR : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hpjR : ((((p ^ j : ℕ))) : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero j hp0)
  have hdiv : N9m m n / p ^ j = 9 * Q9 * n / (m * p ^ j) := by
    rw [N9_eq hm hd, Nat.div_div_eq_div_mul]
  rw [hdiv]
  have he : ((9*Q9:ℕ):ℝ)*((n : ℝ) / (((p ^ j : ℕ)) : ℝ))/((m : ℕ) : ℝ)
      = (((9 * Q9 * n : ℕ)) : ℝ) / (((m * p ^ j : ℕ)) : ℝ) := by
    push_cast
    field_simp
  rw [he]
  exact (intFloor_cast _ _).symm

/-- **Legendre terms of $N_1$ as real floors.** Let $m \ge 1$ divide $Q_9 = 210$, and let
$p \ge 2$, $n$ and $j$ be natural numbers. Write $N_1(m, n) = n \cdot (Q_9/m)$.
Then $\lfloor N_1(m, n)/p^j \rfloor$ equals the floor of the real number $Q_9 (n/p^j)/m$. -/
lemma floor_N1 {m n p j : ℕ} (hm : 1 ≤ m) (hd : m ∣ Q9) (hp2 : 2 ≤ p) :
    ((N1m m n / p ^ j : ℕ) : ℤ)
      = Int.ofNat ⌊((Q9:ℕ):ℝ)*((n : ℝ) / (((p ^ j : ℕ)) : ℝ))/((m : ℕ) : ℝ)⌋₊ := by
  have hp0 : p ≠ 0 := by omega
  have hmp : m * p ^ j ≠ 0 := mul_ne_zero (by omega) (pow_ne_zero j hp0)
  have hmR : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hpjR : ((((p ^ j : ℕ))) : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero j hp0)
  have hdiv : N1m m n / p ^ j = Q9 * n / (m * p ^ j) := by
    rw [N1_eq hm hd, Nat.div_div_eq_div_mul]
  rw [hdiv]
  have he : ((Q9:ℕ):ℝ)*((n : ℝ) / (((p ^ j : ℕ)) : ℝ))/((m : ℕ) : ℝ)
      = (((Q9 * n : ℕ)) : ℝ) / (((m * p ^ j : ℕ)) : ℝ) := by
    push_cast
    field_simp
  rw [he]
  exact (intFloor_cast _ _).symm

-- Legendre in integers.
/-- **Legendre's formula with integer summands.** Let $p$ be a prime and let $N$ and $b$ be
natural numbers with $\lfloor \log_p N \rfloor < b$, where $\lfloor \log_p N \rfloor$ is taken to
be $0$ when $N = 0$. Then the exponent of $p$ in $N!$, as an integer, equals
$\sum_{j=1}^{b-1} \lfloor N / p^j \rfloor$. -/
lemma legendre_sum9 {N p b : ℕ} (hp : p.Prime) (h : Nat.log p N < b) :
    (((N)!.factorization p : ℤ)) = ∑ j ∈ Finset.Ico 1 b, ((N / p ^ j : ℕ) : ℤ) := by
  have hnat := Nat.factorization_factorial hp h
  exact_mod_cast hnat

-- Valuation of a ratio factor in integers (no truncation).
/-- **Valuation of a factorial ratio as a difference of valuations.** Let $Q = 210$, let
$m \ge 1$ be a divisor of $Q$, and let $n$, $p$ be natural numbers. Write $N = n \cdot (Q/m)$
and $R_m(n) = (10N)! / ((9N)! \, N!)$. Then, as integers,
$v_p(R_m(n)) = v_p((10N)!) - v_p((9N)!) - v_p(N!)$, where $v_p(k)$ is the exponent of $p$
in the prime factorization of $k$ (zero when $p$ is not prime). -/
lemma vp_ratio9 {m n p : ℕ} (hm1 : 1 ≤ m) (hd : m ∣ Q9) :
    ((ratio9 m n).factorization p : ℤ)
      = (((N10m m n)!.factorization p : ℤ) - ((N9m m n)!.factorization p : ℤ)
        - ((N1m m n)!.factorization p : ℤ)) := by
  have hdvd := ratio9_dvd m n hm1 hd
  have h9 : (N9m m n)! ≠ 0 := Nat.factorial_ne_zero _
  have h1 : (N1m m n)! ≠ 0 := Nat.factorial_ne_zero _
  have hpos1 : (N9m m n)! * (N1m m n)! ≠ 0 := mul_ne_zero h9 h1
  have hpos2 : (N10m m n)! ≠ 0 := Nat.factorial_ne_zero _
  have hfact := Nat.factorization_div hdvd
  have hle : ((N9m m n)! * (N1m m n)!).factorization
      ≤ ((N10m m n)!).factorization :=
    (Nat.factorization_le_iff_dvd hpos1 hpos2).mpr hdvd
  rw [Finsupp.le_def] at hle
  have hle_p := hle p
  have hmul := Nat.factorization_mul h9 h1
  unfold ratio9
  rw [hfact, Finsupp.tsub_apply, Nat.cast_sub hle_p, hmul, Finsupp.add_apply,
    Nat.cast_add]
  ring

-- Single-factor valuation term.
/-- **One divisor's contribution to the valuation.** For a pair $(m, \varepsilon)$ of a natural
number $m$ and an integer $\varepsilon$, and natural numbers $p$ and $n$, let
$a = \lfloor 210/m \rfloor$ (so $a = 0$ when $m = 0$). The term is the integer
$\varepsilon\bigl(v_p((10na)!) - v_p((9na)!) - v_p((na)!)\bigr)$, where $v_p(k)$ is the exponent
of $p$ in the prime factorization of $k$ (zero when $p$ is not prime). -/
def nu9term (q : ℕ × ℤ) (p n : ℕ) : ℤ :=
  q.2 * (((N10m q.1 n)!.factorization p : ℤ)
    - ((N9m q.1 n)!.factorization p : ℤ)
    - ((N1m q.1 n)!.factorization p : ℤ))

-- Total p-adic valuation of F(n).
/-- **The $p$-adic valuation of the weighted product.** For natural numbers $p$ and $n$,
$\nu_p(n)$ is the integer
$\sum_{d \mid 210} \mu(d)\bigl(v_p((2100n/d)!) - v_p((1890n/d)!) -
v_p((210n/d)!)\bigr)$, where $\mu$ is the Möbius function and $v_p(m)$ is the exponent of $p$
in the prime factorization of $m$ (zero when $p$ is not prime). -/
def nu9 (p n : ℕ) : ℤ :=
  w9.toFinset.sum (fun q : ℕ × ℤ => nu9term q p n)

-- Vanishing of G9r(n/p^j) for large p^j.
/-- **The continuous Breusch function vanishes at small ratios.** Let $p$ be a prime and let
$n \ge 1$ and $j$ be natural numbers. If $p^j > 2100n$, then the continuous Breusch function
$G$ satisfies $G(n/p^j) = 0$. -/
lemma G9r_vanish_of {n p j : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (h : 10 * Q9 * n < p ^ j) : G9r ((n : ℝ) / (((p ^ j : ℕ)) : ℝ)) = 0 := by
  apply G9r_vanish
  · positivity
  · have hpj : 0 < p ^ j := pow_pos hp.pos j
    have hpos : (0 : ℝ) < ((((p ^ j : ℕ))) : ℝ) := by exact_mod_cast hpj
    have hX : (0 : ℝ) < ((((10 * Q9 : ℕ))) : ℝ) := by
      have hQ : 0 < Q9 := Q9_pos
      have hne : 10 * Q9 ≠ 0 := mul_ne_zero (by norm_num) (by omega)
      exact_mod_cast (Nat.pos_of_ne_zero hne)
    have hcast : ((((10 * Q9 * n : ℕ))) : ℝ) < ((((p ^ j : ℕ))) : ℝ) := by
      exact_mod_cast h
    have heq : ((((10 * Q9 * n : ℕ))) : ℝ) = ((((10 * Q9 : ℕ))) : ℝ) * (n : ℝ) := by
      push_cast
      ring
    rw [heq] at hcast
    rw [div_lt_div_iff₀ hpos hX]
    have hcomm : (n : ℝ) * ((((10 * Q9 : ℕ))) : ℝ)
        = ((((10 * Q9 : ℕ))) : ℝ) * (n : ℝ) := by ring
    linarith [hcast, hcomm]

-- The ν-identity: total valuation = Σ_j G9r(n/p^j).
/-- **Valuation identity for the weighted product.** Write $v_p(m)$ for the exponent of $p$ in $m$
and $\mu$ for the Möbius function, and set
$\nu_p(n) = \sum_{d \mid 210} \mu(d)\bigl(v_p((2100n/d)!) - v_p((1890n/d)!) -
v_p((210n/d)!)\bigr)$ and, for real $x \ge 0$,
$G(x) = \sum_{d \mid 210} \mu(d)\bigl(\lfloor 2100x/d \rfloor - \lfloor 1890x/d \rfloor -
\lfloor 210x/d \rfloor\bigr)$. If $p$ is a prime and $n$, $b$ are natural numbers with
$\lfloor \log_p (2100n) \rfloor < b$, where the floor of the logarithm is taken to be $0$ when
$n = 0$, then $\nu_p(n) = \sum_{j=1}^{b-1} G(n/p^j)$. -/
lemma nu9_eq_sum_G {p n b : ℕ} (hp : p.Prime)
    (hb : Nat.log p (10 * Q9 * n) < b) :
    nu9 p n = ∑ j ∈ Finset.Ico 1 b, G9r ((n : ℝ) / (((p ^ j : ℕ)) : ℝ)) := by
  classical
  have hp2 : 2 ≤ p := hp.two_le
  have hlog10 : ∀ q ∈ w9.toFinset, Nat.log p (N10m q.1 n) < b :=
    fun q _ => lt_of_le_of_lt (Nat.log_mono_right N10_le) hb
  have hlog9 : ∀ q ∈ w9.toFinset, Nat.log p (N9m q.1 n) < b :=
    fun q _ => lt_of_le_of_lt (Nat.log_mono_right N9_le) hb
  have hlog1 : ∀ q ∈ w9.toFinset, Nat.log p (N1m q.1 n) < b :=
    fun q _ => lt_of_le_of_lt (Nat.log_mono_right N1_le) hb
  unfold nu9
  have hterm : ∀ q ∈ w9.toFinset, nu9term q p n
      = ∑ j ∈ Finset.Ico 1 b, q.2 * ((((N10m q.1 n / p ^ j : ℕ)) : ℤ)
        - (((N9m q.1 n / p ^ j : ℕ)) : ℤ) - (((N1m q.1 n / p ^ j : ℕ)) : ℤ)) := by
    intro q hq
    unfold nu9term
    rw [legendre_sum9 hp (hlog10 q hq), legendre_sum9 hp (hlog9 q hq),
      legendre_sum9 hp (hlog1 q hq), mul_sub, mul_sub,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  unfold G9r
  apply Finset.sum_congr rfl
  intro q hq
  have hmem : q ∈ w9 := List.mem_toFinset.mp hq
  have hm : 1 ≤ q.1 := w9_pos q hmem
  have hd : q.1 ∣ Q9 := w9_dvd q hmem
  rw [floor_N10 hm hd hp2, floor_N9 hm hd hp2, floor_N1 hm hd hp2]

-- For p^2 > 10Qn, only j = 1 contributes.
/-- **Single-term valuation identity for large primes.** Write $v_p(m)$ for the exponent of $p$
in $m$ and $\mu$ for the Möbius function, and set
$\nu_p(n) = \sum_{d \mid 210} \mu(d)\bigl(v_p((2100n/d)!) - v_p((1890n/d)!) -
v_p((210n/d)!)\bigr)$ and, for real $x \ge 0$,
$G(x) = \sum_{d \mid 210} \mu(d)\bigl(\lfloor 2100x/d \rfloor - \lfloor 1890x/d \rfloor -
\lfloor 210x/d \rfloor\bigr)$. If $p$ is a prime and $n \ge 1$ is a natural number with
$2100n < p^2$, then $\nu_p(n) = G(n/p)$. -/
lemma nu9_eq_single {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hbig : 10 * Q9 * n < p ^ 2) : nu9 p n = G9r ((n : ℝ) / (((p : ℕ)) : ℝ)) := by
  set b : ℕ := Nat.log p (10 * Q9 * n) + 2 with hb_def
  have hb : Nat.log p (10 * Q9 * n) < b := by omega
  rw [nu9_eq_sum_G hp hb]
  have hsplit : Finset.Ico 1 b = insert 1 (Finset.Ico 2 b) := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp only [Finset.mem_Ico]; omega)]
  have hzero : ∑ j ∈ Finset.Ico 2 b, G9r ((n : ℝ) / (((p ^ j : ℕ)) : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hpow : p ^ 2 ≤ p ^ j := pow_le_pow_right₀ hp.pos hj.1
    have h : 10 * Q9 * n < p ^ j := lt_of_lt_of_le hbig hpow
    exact G9r_vanish_of hp hn h
  rw [hzero, add_zero, pow_one]

/-- **Value of $10Qn$.** Let $Q = 210$ be the truncation modulus. For every natural number $n$,
$10 \cdot Q \cdot n = 2100n$. -/
lemma U9_10Q9 (n : ℕ) : 10 * Q9 * n = 2100 * n := by rw [Q9_eq]

/-- **Logarithm of a natural number from its factorization.** For every nonzero natural number
$K$, $\log K = \sum_{p} v_p(K) \log p$, where $p$ runs over the prime divisors of $K$ and
$v_p(K)$ is the exponent of $p$ in the prime factorization of $K$. -/
lemma U9_log_fact (K : ℕ) (hK : K ≠ 0) :
    Real.log ((K : ℕ) : ℝ) =
      ∑ p ∈ K.factorization.support, ((K.factorization p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
  have hprod := Nat.prod_factorization_pow_eq_self hK
  have hcast : ((K : ℕ) : ℝ)
      = ∏ p ∈ K.factorization.support, ((((p : ℕ)) : ℝ) ^ K.factorization p) := by
    have h2 := congrArg (Nat.cast : ℕ → ℝ) hprod
    have hdef : K.factorization.prod (fun p e => p ^ e)
        = ∏ p ∈ K.factorization.support, p ^ K.factorization p := rfl
    rw [hdef, Nat.cast_prod] at h2
    simpa using h2.symm
  rw [hcast, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p _
    rw [Real.log_pow]
  · intro p hp
    have hpmem : p ∈ K.primeFactors := Nat.support_factorization K ▸ hp
    have hpp := Nat.prime_of_mem_primeFactors hpmem
    have hp0 : (p : ℕ) ≠ 0 := ne_of_gt hpp.pos
    exact pow_ne_zero _ (by exact_mod_cast hp0)

/-- **Bound on the prime factors of the ratio factors.** Let $(m, \mu)$ be an entry of the
divisor table $w_9$ (so $m$ divides $210$ and $\mu$ is the Möbius value of $m$), let $n$ be a
natural number and put $d = 210/m$. Then every prime factor of $(10nd)!/((9nd)!\,(nd)!)$ is at
most $2100n$. -/
lemma U9_supp_sub (q : ℕ × ℤ) (hq : q ∈ w9) (n : ℕ) :
    (ratio9 q.1 n).factorization.support ⊆ Nat.primesBelow (2100 * n + 1) := by
  intro p hp
  have hpmem : p ∈ (ratio9 q.1 n).primeFactors :=
    Nat.support_factorization _ ▸ hp
  have hpp := Nat.prime_of_mem_primeFactors hpmem
  have hdvdR : p ∣ ratio9 q.1 n := Nat.dvd_of_mem_primeFactors hpmem
  have hm1 : 1 ≤ q.1 := w9_pos q hq
  have hd : q.1 ∣ Q9 := w9_dvd q hq
  have hRdvd : ratio9 q.1 n ∣ (N10m q.1 n)! := by
    have h := ratio9_dvd q.1 n hm1 hd
    exact ⟨_, (Nat.div_mul_cancel h).symm⟩
  have hpF : p ∣ (N10m q.1 n)! := dvd_trans hdvdR hRdvd
  have hleN : p ≤ N10m q.1 n := (Nat.Prime.dvd_factorial hpp).mp hpF
  have hleX : p ≤ 2100 * n := by
    have h := N10_le (m := q.1) (n := n)
    rw [Q9_eq] at h
    omega
  rw [Nat.mem_primesBelow]
  exact ⟨by omega, hpp⟩

/-- **Valuation term of one binomial factor.** Let $Q = 210$, let $m \ge 1$ be a divisor of $Q$,
let $w$ be an integer, and let $p$ and $n$ be natural numbers. Put $N = n \cdot (Q/m)$ and
$R = (10N)!/((9N)!\,N!)$. For a natural number $a$, write $v_p(a)$ for the exponent of $p$ in
the prime factorization of $a$ (zero when $p$ is not prime). Then
$w \, (v_p((10N)!) - v_p((9N)!) - v_p(N!)) = w \, v_p(R)$. -/
lemma U9_nu9term_eq (q : ℕ × ℤ) (p n : ℕ) (hm1 : 1 ≤ q.1) (hd : q.1 ∣ Q9) :
    ((nu9term q p n : ℤ) : ℝ)
      = (q.2 : ℝ) * (((ratio9 q.1 n).factorization p : ℕ) : ℝ) := by
  unfold nu9term
  have h := vp_ratio9 (m := q.1) (n := n) (p := p) hm1 hd
  rw [← h, Int.cast_mul]
  simp

/-- **Valuation terms vanish off the prime support.** Let $m \ge 1$ be a divisor of $Q_9 = 210$,
let $\mu$ be an integer, let $p$ and $n$ be natural numbers, and put $d = 210/m$. For a natural
number $k$ write $v_p(k)$ for the exponent of $p$ in the prime factorization of $k$ (zero when
$p$ is not prime). If $v_p\bigl((10nd)!/((9nd)!\,(nd)!)\bigr) = 0$, then the valuation term
$\mu\,\bigl(v_p((10nd)!) - v_p((9nd)!) - v_p((nd)!)\bigr)$ of the pair $(m, \mu)$ at $p$ and $n$
is $0$. -/
lemma U9_nu9term_zero (q : ℕ × ℤ) (p n : ℕ) (hm1 : 1 ≤ q.1) (hd : q.1 ∣ Q9)
    (h0 : (ratio9 q.1 n).factorization p = 0) : nu9term q p n = 0 := by
  unfold nu9term
  have h := vp_ratio9 (m := q.1) (n := n) (p := p) hm1 hd
  rw [h0, Nat.cast_zero] at h
  rw [← h, mul_zero]

/-- **A weighted log-factor as a sum over primes.** Let $(m, \mu)$ be an entry of the divisor
table $w_9$ (so $m$ divides $210$ and $\mu$ is the Möbius value of $m$), let $n \ge 1$ be a
natural number, put $d = 210/m$ and $R = (10nd)!/((9nd)!\,(nd)!)$, and for a prime $p$ write
$\nu_p = \mu\,\bigl(v_p((10nd)!) - v_p((9nd)!) - v_p((nd)!)\bigr)$, where $v_p(k)$ is the
exponent of $p$ in the prime factorization of $k$. Then $\mu \log R$ equals the sum of
$\nu_p \log p$ over all primes $p \le 2100n$. -/
lemma U9_q_expand (q : ℕ × ℤ) (hq : q ∈ w9) (n : ℕ) (hn : 1 ≤ n) :
    (q.2 : ℝ) * Real.log ((ratio9 q.1 n : ℕ) : ℝ)
      = ∑ p ∈ Nat.primesBelow (2100 * n + 1),
        ((nu9term q p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
  have hm1 : 1 ≤ q.1 := w9_pos q hq
  have hd : q.1 ∣ Q9 := w9_dvd q hq
  have hRne : ratio9 q.1 n ≠ 0 := ne_of_gt (ratio9_pos _ _ hn hm1 hd)
  have hterm : ∀ p ∈ (ratio9 q.1 n).factorization.support,
      (q.2 : ℝ) * (((((ratio9 q.1 n).factorization p : ℕ)) : ℝ) * Real.log ((p : ℕ) : ℝ))
        = (((nu9term q p n : ℤ)) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
    intro p _
    rw [U9_nu9term_eq q p n hm1 hd]
    ring
  calc (q.2 : ℝ) * Real.log ((ratio9 q.1 n : ℕ) : ℝ)
      = ∑ p ∈ (ratio9 q.1 n).factorization.support,
          (q.2 : ℝ) * (((((ratio9 q.1 n).factorization p : ℕ)) : ℝ)
            * Real.log ((p : ℕ) : ℝ)) := by
        rw [U9_log_fact _ hRne, Finset.mul_sum]
    _ = ∑ p ∈ (ratio9 q.1 n).factorization.support,
          (((nu9term q p n : ℤ)) : ℝ) * Real.log ((p : ℕ) : ℝ) :=
        Finset.sum_congr rfl hterm
    _ = ∑ p ∈ Nat.primesBelow (2100 * n + 1),
          (((nu9term q p n : ℤ)) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
        apply Finset.sum_subset (U9_supp_sub q hq n)
        intro p _ hpnot
        have h0 : (ratio9 q.1 n).factorization p = 0 :=
          Finsupp.notMem_support_iff.mp hpnot
        rw [U9_nu9term_zero q p n hm1 hd h0, Int.cast_zero, zero_mul]

/-- **Prime factorization of $\log F_9(n)$.** Let $n \ge 1$ be a natural number. For each divisor
$m$ of $210$ put $N_m = 210n/m$, let $\mu$ be the Möbius function, and let
$F_9(n) = \prod_{m \mid 210} \binom{10N_m}{N_m}^{\mu(m)}$. For a prime $p$ let $v_p$ denote the
$p$-adic valuation and put
$\nu_9(p, n) = \sum_{m \mid 210} \mu(m) (v_p((10N_m)!) - v_p((9N_m)!) - v_p(N_m!))$, the
$p$-adic valuation of $F_9(n)$. Then $\log F_9(n) = \sum_{p \le 2100n} \nu_9(p, n) \log p$, where
$p$ runs over the primes at most $2100n$. -/
lemma U9_bridge (n : ℕ) (hn : 1 ≤ n) :
    logF9 n = ∑ p ∈ Nat.primesBelow (2100 * n + 1),
      ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
  classical
  unfold logF9
  have hexp : ∀ q ∈ w9.toFinset,
      (q.2 : ℝ) * Real.log ((ratio9 q.1 n : ℕ) : ℝ)
        = ∑ p ∈ Nat.primesBelow (2100 * n + 1),
          (((nu9term q p n : ℤ)) : ℝ) * Real.log ((p : ℕ) : ℝ) :=
    fun q hq => U9_q_expand q (List.mem_toFinset.mp hq) n hn
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  unfold nu9
  rw [Int.cast_sum, Finset.sum_mul]

/-- **Logarithms of primes are nonnegative.** For every prime $p$, $\log p \ge 0$. -/
lemma U9_logp_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log ((p : ℕ) : ℝ) := by
  have h1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp.two_le
    linarith
  exact Real.log_nonneg h1

/-- **$G$ is at most its positive part.** For real $y$ let
$G(y) = \sum_{m \mid 210} \mu(m) (\lfloor 2100y/m \rfloor_+ - \lfloor 1890y/m \rfloor_+ -
\lfloor 210y/m \rfloor_+)$, where $\mu$ is the Möbius function and
$\lfloor t \rfloor_+ = \max(\lfloor t \rfloor, 0)$. For every real number $x$,
$G(x) \le \max(G(x), 0)$. -/
lemma U9_G_toNat (x : ℝ) : ((G9r x : ℤ) : ℝ) ≤ ((((G9r x).toNat : ℕ)) : ℝ) := by
  rcases le_total (G9r x) 0 with h | h
  · rw [Int.toNat_eq_zero.mpr h, Nat.cast_zero]
    exact_mod_cast h
  · have e : ((((G9r x).toNat : ℕ)) : ℝ) = ((G9r x : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
    rw [e]

/-- **The truncated continuous Breusch function is at most 3.** For every real $x \ge 0$, the
continuous Breusch function $G$ satisfies $\max(G(x), 0) \le 3$. -/
lemma U9_toNat_le3 (x : ℝ) (hx : 0 ≤ x) : (G9r x).toNat ≤ 3 := by
  have h := G9r_le3 x hx
  have h2 := Int.toNat_le_toNat h
  have h3 : (3 : ℤ).toNat = 3 := rfl
  rwa [h3] at h2

/-- **Positive lower bounds on a truncation lift to the integer.** Let $z$ be an integer and let
$i \ge 1$ be a natural number. If $i \le \max(z, 0)$, then $i \le z$. -/
lemma U9_of_toNat {z : ℤ} {i : ℕ} (hi : 1 ≤ i) (h : i ≤ z.toNat) :
    (i : ℤ) ≤ z := by
  have hz : 0 ≤ z := by
    by_contra hc
    push Not at hc
    have h0 : z.toNat = 0 := Int.toNat_eq_zero.mpr (le_of_lt hc)
    omega
  have e : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz
  have h2 : ((i : ℕ) : ℤ) ≤ ((z.toNat : ℕ) : ℤ) := by exact_mod_cast h
  rwa [e] at h2

/-- **Layer-cake decomposition with three levels.** Let $B$ be a finite set of natural numbers,
let $M : \mathbb{N} \to \mathbb{N}$ and $c : \mathbb{N} \to \mathbb{R}$, and suppose $M(p) \le 3$
for every $p \in B$. Then
$\sum_{p \in B} M(p) c(p) = \sum_{i=1}^{3} \sum_{p \in B,\, M(p) \ge i} c(p)$. -/
lemma U9_layercake (B : Finset ℕ) (M : ℕ → ℕ) (c : ℕ → ℝ)
    (hM : ∀ p ∈ B, M p ≤ 3) :
    ∑ p ∈ B, ((M p : ℕ) : ℝ) * c p
      = ∑ i ∈ Finset.Icc 1 3, ∑ p ∈ B.filter (fun p => i ≤ M p), c p := by
  classical
  have h1 : ∀ p ∈ B, ((M p : ℕ) : ℝ)
      = ∑ i ∈ Finset.Icc 1 3, (if i ≤ M p then (1 : ℝ) else 0) := by
    intro p hp
    have hMp3 := hM p hp
    have hfeq : (Finset.Icc 1 3).filter (fun i => i ≤ M p)
        = Finset.Icc 1 (M p) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    have hc : (Finset.Icc 1 (M p)).card = M p := by
      rw [Nat.card_Icc]
      omega
    calc ((M p : ℕ) : ℝ)
        = (((Finset.Icc 1 3).filter (fun i => i ≤ M p)).card : ℝ) := by
          rw [hfeq, hc]
      _ = ∑ i ∈ Finset.Icc 1 3, (if i ≤ M p then (1 : ℝ) else 0) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hMp : ∀ p ∈ B, ((M p : ℕ) : ℝ) * c p
      = ∑ i ∈ Finset.Icc 1 3, (if i ≤ M p then c p else 0) := by
    intro p hp
    calc ((M p : ℕ) : ℝ) * c p
        = (∑ i ∈ Finset.Icc 1 3, (if i ≤ M p then (1 : ℝ) else 0)) * c p := by
          rw [h1 p hp]
      _ = ∑ i ∈ Finset.Icc 1 3, (if i ≤ M p then c p else 0) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs with hi
          · ring
          · ring
  rw [Finset.sum_congr rfl hMp, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_filter]

/-- **A level bound turns into a bound on the prime.** Let $n \ge 1$ be a natural number, $p$ a
prime and $j \ge 1$ a real number. If $j / 18900 \le n / p$, then $p \le 18900\,n / j$. -/
lemma U9_ple_of_G (n p : ℕ) (_hn : 1 ≤ n) (hp : p.Prime)
    (jm : ℝ) (hjm : 1 ≤ jm)
    (hlvl : jm / 18900 ≤ (n : ℝ) / ((p : ℕ) : ℝ)) :
    ((p : ℕ) : ℝ) ≤ 18900 * (n : ℝ) / jm := by
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.pos
  have hjm0 : (0 : ℝ) < jm := lt_of_lt_of_le zero_lt_one hjm
  have h18900 : (0 : ℝ) < 18900 := by norm_num
  have hcross : jm * ((p : ℕ) : ℝ) ≤ (n : ℝ) * 18900 := by
    have h1 : (jm / 18900) * ((p : ℕ) : ℝ) ≤ (n : ℝ) := (le_div_iff₀ hp0).mp hlvl
    have h2 : ((jm / 18900) * ((p : ℕ) : ℝ)) * 18900 ≤ (n : ℝ) * 18900 :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt h18900)
    have e : ((jm / 18900) * ((p : ℕ) : ℝ)) * 18900 = jm * ((p : ℕ) : ℝ) := by
      ring
    linarith [h2, e]
  rw [le_div_iff₀ hjm0]
  linarith [hcross]

/-- **Primes up to $1890n$ have $n/p \ge 1/1890$.** Let $Q = 210$ be the truncation modulus, let
$n \ge 1$ be a natural number and let $p$ be a prime with $p \le 1890 n$. Then
$1/(9Q) \le n/p$, where $9Q = 1890$. -/
lemma U9_xlo (n p : ℕ) (_hn : 1 ≤ n) (hp : p.Prime) (hle : p ≤ 1890 * n) :
    1 / (((9 * Q9 : ℕ)) : ℝ) ≤ (n : ℝ) / ((p : ℕ) : ℝ) := by
  have h9Q : (((9 * Q9 : ℕ)) : ℝ) = 1890 := by
    have hnat : (9 * Q9 : ℕ) = 1890 := by decide
    rw [hnat]
    norm_num
  rw [h9Q]
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.pos
  rw [le_div_iff₀ hp0]
  have hleR : ((p : ℕ) : ℝ) ≤ 1890 * (n : ℝ) := by exact_mod_cast hle
  linarith [hleR]

/-- **Upper bound for primes where a Möbius-weighted floor sum is at least 1.** For real
$x \ge 0$ let $G(x) = \sum_{m \mid 210} \mu(m)\bigl(\lfloor 2100x/m \rfloor -
\lfloor 1890x/m \rfloor - \lfloor 210x/m \rfloor\bigr)$, where $\mu$ is the Möbius function.
Let $n \ge 1$ be a natural number and $p \le 1890n$ a prime. If $G(n/p) \ge 1$, then
$p \le 18900n/279$. -/
lemma U9_ple1 (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime)
    (hle : p ≤ 1890 * n) (hG : (1 : ℤ) ≤ G9r ((n : ℝ) / ((p : ℕ) : ℝ))) :
    ((p : ℕ) : ℝ) ≤ 18900 * (n : ℝ) / 279 := by
  apply U9_ple_of_G n p hn hp 279 (by norm_num)
  exact G9r_level1 _ (U9_xlo n p hn hp hle) hG

/-- **Upper bound for primes where a Möbius-weighted floor sum is at least 2.** For real
$x \ge 0$ let $G(x) = \sum_{m \mid 210} \mu(m)\bigl(\lfloor 2100x/m \rfloor -
\lfloor 1890x/m \rfloor - \lfloor 210x/m \rfloor\bigr)$, where $\mu$ is the Möbius function.
Let $n \ge 1$ be a natural number and $p \le 1890n$ a prime. If $G(n/p) \ge 2$, then
$p \le 18900n/657$. -/
lemma U9_ple2 (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime)
    (hle : p ≤ 1890 * n) (hG : (2 : ℤ) ≤ G9r ((n : ℝ) / ((p : ℕ) : ℝ))) :
    ((p : ℕ) : ℝ) ≤ 18900 * (n : ℝ) / 657 := by
  apply U9_ple_of_G n p hn hp 657 (by norm_num)
  exact G9r_level2 _ (U9_xlo n p hn hp hle) hG

/-- **Upper bound for primes where a Möbius-weighted floor sum is at least 3.** For real
$x \ge 0$ let $G(x) = \sum_{m \mid 210} \mu(m)\bigl(\lfloor 2100x/m \rfloor -
\lfloor 1890x/m \rfloor - \lfloor 210x/m \rfloor\bigr)$, where $\mu$ is the Möbius function.
Let $n \ge 1$ be a natural number and $p \le 1890n$ a prime. If $G(n/p) \ge 3$, then
$p \le 18900n/963$. -/
lemma U9_ple3 (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime)
    (hle : p ≤ 1890 * n) (hG : (3 : ℤ) ≤ G9r ((n : ℝ) / ((p : ℕ) : ℝ))) :
    ((p : ℕ) : ℝ) ≤ 18900 * (n : ℝ) / 963 := by
  apply U9_ple_of_G n p hn hp 963 (by norm_num)
  exact G9r_level3 _ (U9_xlo n p hn hp hle) hG

/-- **The primorial as a product of primes.** For every natural number $k$, the primorial $k\#$
equals the product of all primes $p$ with $p < k + 1$. -/
lemma U9_primorial_eq (k : ℕ) :
    primorial k = ∏ p ∈ Nat.primesBelow (k + 1), p := by
  have hset : Nat.primesBelow (k + 1)
      = (Finset.range (k + 1)).filter (fun p => p.Prime) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primesBelow]
  unfold primorial
  rw [hset]

/-- **Chebyshev-type bound for the sum of prime logarithms.** For every real number $Y \ge 0$,
the sum of $\log p$ over all primes $p \le \lfloor Y \rfloor$ is at most $Y \log 3.4$. -/
lemma U9_theta_le (Y : ℝ) (hY : 0 ≤ Y) :
    ∑ p ∈ Nat.primesBelow (⌊Y⌋₊ + 1), Real.log ((p : ℕ) : ℝ)
      ≤ Y * Real.log 3.4 := by
  classical
  have hpos : (0 : ℝ) < (((primorial ⌊Y⌋₊ : ℕ)) : ℝ) := by
    have h := primorial_pos ⌊Y⌋₊
    exact_mod_cast h
  have hprod : (∏ p ∈ Nat.primesBelow (⌊Y⌋₊ + 1), ((p : ℕ) : ℝ))
      = (((primorial ⌊Y⌋₊ : ℕ)) : ℝ) := by
    rw [← Nat.cast_prod, U9_primorial_eq]
  have hne : ∀ p ∈ Nat.primesBelow (⌊Y⌋₊ + 1), (((p : ℕ) : ℝ) ≠ 0) := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    have hp0 : p ≠ 0 := ne_of_gt hp.2.pos
    exact_mod_cast hp0
  have hlog : ∑ p ∈ Nat.primesBelow (⌊Y⌋₊ + 1), Real.log ((p : ℕ) : ℝ)
      = Real.log (((primorial ⌊Y⌋₊ : ℕ)) : ℝ) := by
    rw [← hprod, Real.log_prod hne]
  have hle := theta34_real hY
  have h34 : (0 : ℝ) < 3.4 := by norm_num
  have hlogle : Real.log (((primorial ⌊Y⌋₊ : ℕ)) : ℝ) ≤ Y * Real.log 3.4 := by
    have h1 := Real.log_le_log hpos hle
    rwa [Real.log_rpow h34] at h1
  rw [hlog]
  exact hlogle

/-- **Prime-logarithm bound for one level of $G$.** For real $x \ge 0$ let
$G(x) = \sum_{m \mid 210} \mu(m) (\lfloor 2100x/m \rfloor - \lfloor 1890x/m \rfloor -
\lfloor 210x/m \rfloor)$, where $\mu$ is the Möbius function. Let $n \ge 1$ be a natural number,
let $B$ be a finite set of primes $p$ with $p \le 1890n$, let $i \ge 1$ be a natural number, and
let $j \ge 1$ be a real number with $18900n/j \ge 0$. Suppose that every prime $p \le 1890n$ with
$G(n/p) \ge i$ satisfies $p \le 18900n/j$. Then the sum of $\log p$ over the $p \in B$ with
$\max(G(n/p), 0) \ge i$ is at most $(18900n/j) \log 3.4$. -/
lemma U9_Bi_le (n : ℕ) (_hn : 1 ≤ n) (B : Finset ℕ)
    (hBmem : ∀ p ∈ B, p.Prime ∧ p ≤ 1890 * n)
    (i : ℕ) (hi : 1 ≤ i) (jm : ℝ) (_hjm : 1 ≤ jm)
    (hle_i : ∀ p : ℕ, p.Prime → p ≤ 1890 * n → (i : ℤ) ≤ G9r ((n : ℝ) / ((p : ℕ) : ℝ)) →
      ((p : ℕ) : ℝ) ≤ 18900 * (n : ℝ) / jm)
    (hYnn : 0 ≤ 18900 * (n : ℝ) / jm) :
    ∑ p ∈ B.filter (fun p => i ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
        Real.log ((p : ℕ) : ℝ)
      ≤ 18900 * (n : ℝ) / jm * Real.log 3.4 := by
  classical
  have hsub : B.filter (fun p => i ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat)
      ⊆ Nat.primesBelow (⌊18900 * (n : ℝ) / jm⌋₊ + 1) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpB, hiM⟩ := hp
    obtain ⟨hpp, hle⟩ := hBmem p hpB
    have hG := U9_of_toNat hi hiM
    have hple := hle_i p hpp hle hG
    have hpfloor : p ≤ ⌊18900 * (n : ℝ) / jm⌋₊ := Nat.le_floor hple
    rw [Nat.mem_primesBelow]
    exact ⟨by omega, hpp⟩
  calc ∑ p ∈ B.filter (fun p => i ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
          Real.log ((p : ℕ) : ℝ)
      ≤ ∑ p ∈ Nat.primesBelow (⌊18900 * (n : ℝ) / jm⌋₊ + 1),
          Real.log ((p : ℕ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by
          intro p hp _
          exact U9_logp_nonneg (Nat.mem_primesBelow.mp hp).2)
    _ ≤ 18900 * (n : ℝ) / jm * Real.log 3.4 := U9_theta_le _ hYnn

/-- **Contribution of primes with $p^2 > 2100n$.** Write $v_p(m)$ for the exponent of $p$ in $m$
and $\mu$ for the Möbius function, and set
$\nu_p(n) = \sum_{d \mid 210} \mu(d)\bigl(v_p((2100n/d)!) - v_p((1890n/d)!) -
v_p((210n/d)!)\bigr)$. For every natural number $n \ge 1$, the sum of $\nu_p(n) \log p$ over the
primes $p \le 1890n$ with $p^2 > 2100n$ satisfies

$$
\sum_{\substack{p \le 1890n \text{ prime} \\ p^2 > 2100n}} \nu_p(n) \log p \le
\left(\frac{18900}{279} + \frac{18900}{657} + \frac{18900}{963}\right) n \log 3.4.
$$
-/
lemma U9_B_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ ((Nat.primesBelow (2100 * n + 1)).filter (fun p => p ≤ 1890 * n)).filter
      (fun p => 2100 * n < p ^ 2),
      ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
    ≤ (18900 / 279 + 18900 / 657 + 18900 / 963 : ℝ) * (n : ℝ) * Real.log 3.4 := by
  classical
  set B := ((Nat.primesBelow (2100 * n + 1)).filter (fun p => p ≤ 1890 * n)).filter
    (fun p => 2100 * n < p ^ 2) with hBdef
  have hBmem : ∀ p ∈ B, p.Prime ∧ p ≤ 1890 * n := by
    intro p hp
    rw [hBdef, Finset.mem_filter] at hp
    obtain ⟨hpT, -⟩ := hp
    rw [Finset.mem_filter] at hpT
    obtain ⟨hpS, hle⟩ := hpT
    exact ⟨(Nat.mem_primesBelow.mp hpS).2, hle⟩
  have hsq : ∀ p ∈ B, 2100 * n < p ^ 2 := by
    intro p hp
    rw [hBdef, Finset.mem_filter] at hp
    exact hp.2
  have hsingle : ∀ p ∈ B, ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      = ((G9r ((n : ℝ) / ((p : ℕ) : ℝ)) : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
    intro p hp
    obtain ⟨hpp, -⟩ := hBmem p hp
    have hbig : 10 * Q9 * n < p ^ 2 := by rw [U9_10Q9 n]; exact hsq p hp
    rw [nu9_eq_single hpp hn hbig]
  have hMle : ∀ p ∈ B,
      ((G9r ((n : ℝ) / ((p : ℕ) : ℝ)) : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      ≤ ((((G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat : ℕ)) : ℝ)
        * Real.log ((p : ℕ) : ℝ) := by
    intro p hp
    obtain ⟨hpp, -⟩ := hBmem p hp
    exact mul_le_mul_of_nonneg_right (U9_G_toNat _) (U9_logp_nonneg hpp)
  have hM3 : ∀ p ∈ B, (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat ≤ 3 := by
    intro p hp
    apply U9_toNat_le3
    positivity
  have hLc := U9_layercake B (fun p => (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat)
    (fun p => Real.log ((p : ℕ) : ℝ)) hM3
  have hLc' : ∑ p ∈ B,
        ((((G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat : ℕ)) : ℝ)
          * Real.log ((p : ℕ) : ℝ)
      = ∑ i ∈ Finset.Icc 1 3,
        ∑ p ∈ B.filter (fun p => i ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
        Real.log ((p : ℕ) : ℝ) := hLc
  have hexpand : ∑ p ∈ B,
        ((((G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat : ℕ)) : ℝ)
          * Real.log ((p : ℕ) : ℝ)
      = (∑ p ∈ B.filter (fun p => 1 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
          Real.log ((p : ℕ) : ℝ))
        + ((∑ p ∈ B.filter (fun p => 2 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
          Real.log ((p : ℕ) : ℝ))
        + (∑ p ∈ B.filter (fun p => 3 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
          Real.log ((p : ℕ) : ℝ))) := by
    have e1 := hLc'
    rw [show Finset.Icc 1 3 = {1, 2, 3} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at e1
    exact e1
  have g1 : (∑ p ∈ B.filter (fun p => 1 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
        Real.log ((p : ℕ) : ℝ)) ≤ 18900 * (n : ℝ) / 279 * Real.log 3.4 :=
    U9_Bi_le n hn B hBmem 1 (by norm_num) 279 (by norm_num)
      (fun p hpp hle hG => U9_ple1 n p hn hpp hle (by simpa using hG)) (by positivity)
  have g2 : (∑ p ∈ B.filter (fun p => 2 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
        Real.log ((p : ℕ) : ℝ)) ≤ 18900 * (n : ℝ) / 657 * Real.log 3.4 :=
    U9_Bi_le n hn B hBmem 2 (by norm_num) 657 (by norm_num)
      (fun p hpp hle hG => U9_ple2 n p hn hpp hle (by simpa using hG)) (by positivity)
  have g3 : (∑ p ∈ B.filter (fun p => 3 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
        Real.log ((p : ℕ) : ℝ)) ≤ 18900 * (n : ℝ) / 963 * Real.log 3.4 :=
    U9_Bi_le n hn B hBmem 3 (by norm_num) 963 (by norm_num)
      (fun p hpp hle hG => U9_ple3 n p hn hpp hle (by simpa using hG)) (by positivity)
  have hcoef : (18900 * (n : ℝ) / 279 + (18900 * (n : ℝ) / 657
      + 18900 * (n : ℝ) / 963)) * Real.log 3.4
      = (18900 / 279 + 18900 / 657 + 18900 / 963 : ℝ) * (n : ℝ) * Real.log 3.4 := by
    ring
  calc ∑ p ∈ B, ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      = ∑ p ∈ B, ((G9r ((n : ℝ) / ((p : ℕ) : ℝ)) : ℤ) : ℝ)
        * Real.log ((p : ℕ) : ℝ) := Finset.sum_congr rfl hsingle
    _ ≤ ∑ p ∈ B, ((((G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat : ℕ)) : ℝ)
        * Real.log ((p : ℕ) : ℝ) := Finset.sum_le_sum hMle
    _ = (∑ p ∈ B.filter (fun p => 1 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
          Real.log ((p : ℕ) : ℝ))
        + ((∑ p ∈ B.filter (fun p => 2 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
          Real.log ((p : ℕ) : ℝ))
        + (∑ p ∈ B.filter (fun p => 3 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
          Real.log ((p : ℕ) : ℝ))) := hexpand
    _ ≤ (18900 * (n : ℝ) / 279 + (18900 * (n : ℝ) / 657
        + 18900 * (n : ℝ) / 963)) * Real.log 3.4 := by
        have hle := add_le_add (add_le_add g1 g2) g3
        linarith [hle]
    _ = (18900 / 279 + 18900 / 657 + 18900 / 963 : ℝ) * (n : ℝ) * Real.log 3.4 :=
        hcoef

/-- **Bound for one small-square prime term.** Let $n \ge 1$ be a natural number and let $p$ be a
prime with $p^2 \le 2100n$. For each divisor $m$ of $210$ put $N_m = 210n/m$, let $\mu$ be the
Möbius function and $v_p$ the $p$-adic valuation, and put
$\nu_9(p, n) = \sum_{m \mid 210} \mu(m) (v_p((10N_m)!) - v_p((9N_m)!) - v_p(N_m!))$. Then
$\nu_9(p, n) \log p \le 3 \log(2100n)$. -/
lemma U9_Cterm_le (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime)
    (_hleX : p ^ 2 ≤ 2100 * n) :
    ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      ≤ 3 * Real.log (((2100 * n : ℕ)) : ℝ) := by
  have hXpos : 0 < 2100 * n := by omega
  have hXne : (2100 * n : ℕ) ≠ 0 := ne_of_gt hXpos
  have hnu : nu9 p n
      = ∑ j ∈ Finset.Ico 1 (Nat.log p (10 * Q9 * n) + 2),
        G9r ((n : ℝ) / ((((p ^ j : ℕ))) : ℝ)) := nu9_eq_sum_G hp (by omega)
  have hvan : ∀ j ∈ Finset.Ico 1 (Nat.log p (10 * Q9 * n) + 2),
      j ∉ Finset.Icc 1 (Nat.log p (2100 * n)) →
      G9r ((n : ℝ) / ((((p ^ j : ℕ))) : ℝ)) = 0 := by
    intro j hjIco hjIcc
    rw [Finset.mem_Ico] at hjIco
    rw [Finset.mem_Icc] at hjIcc
    have hLt : Nat.log p (2100 * n) < j := by
      by_contra hc
      push Not at hc
      exact hjIcc ⟨hjIco.1, hc⟩
    have hle : ¬ p ^ j ≤ 2100 * n := by
      intro hlej
      have hlj := Nat.le_log_of_pow_le hp.one_lt hlej
      omega
    have hlt : 2100 * n < p ^ j := lt_of_not_ge hle
    have h10 : 10 * Q9 * n < p ^ j := by rw [U9_10Q9 n]; exact hlt
    exact G9r_vanish_of hp hn h10
  have hsub : Finset.Icc 1 (Nat.log p (2100 * n))
      ⊆ Finset.Ico 1 (Nat.log p (10 * Q9 * n) + 2) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_Ico]
    have hlog_eq : Nat.log p (10 * Q9 * n) = Nat.log p (2100 * n) := by
      rw [U9_10Q9 n]
    omega
  have hsplit : (∑ j ∈ Finset.Ico 1 (Nat.log p (10 * Q9 * n) + 2),
        G9r ((n : ℝ) / ((((p ^ j : ℕ))) : ℝ)))
      = ∑ j ∈ Finset.Icc 1 (Nat.log p (2100 * n)),
        G9r ((n : ℝ) / ((((p ^ j : ℕ))) : ℝ)) :=
    (Finset.sum_subset hsub (fun j hjIco hjNIcc => hvan j hjIco hjNIcc)).symm
  have hbd : (∑ j ∈ Finset.Icc 1 (Nat.log p (2100 * n)),
        G9r ((n : ℝ) / ((((p ^ j : ℕ))) : ℝ)))
      ≤ (Nat.log p (2100 * n) : ℤ) * 3 := by
    calc _ ≤ ∑ _j ∈ Finset.Icc 1 (Nat.log p (2100 * n)), (3 : ℤ) :=
          Finset.sum_le_sum (fun j _ => G9r_le3 _ (by positivity))
      _ = (Nat.log p (2100 * n) : ℤ) * 3 := by
          have hc : (Finset.Icc 1 (Nat.log p (2100 * n))).card
              = Nat.log p (2100 * n) := by
            rw [Nat.card_Icc]
            omega
          rw [Finset.sum_const, nsmul_eq_mul, hc]
  have hnu_le : (nu9 p n : ℤ) ≤ (Nat.log p (2100 * n) : ℤ) * 3 := by
    rw [hnu, hsplit]
    exact hbd
  have hpow : p ^ Nat.log p (2100 * n) ≤ 2100 * n :=
    Nat.pow_log_le_self p hXne
  have hpowR : ((((p : ℕ)) : ℝ) ^ Nat.log p (2100 * n))
      ≤ (((2100 * n : ℕ)) : ℝ) := by
    exact_mod_cast hpow
  have hpR : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.pos
  have hlogLp : ((Nat.log p (2100 * n) : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      ≤ Real.log (((2100 * n : ℕ)) : ℝ) := by
    have h1 : Real.log ((((p : ℕ)) : ℝ) ^ Nat.log p (2100 * n))
        ≤ Real.log (((2100 * n : ℕ)) : ℝ) :=
      Real.log_le_log (pow_pos hpR _) hpowR
    rwa [Real.log_pow] at h1
  have hnuR : ((nu9 p n : ℤ) : ℝ)
      ≤ ((Nat.log p (2100 * n) : ℕ) : ℝ) * 3 := by
    exact_mod_cast hnu_le
  have hlogp := U9_logp_nonneg hp
  calc ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      ≤ ((((Nat.log p (2100 * n) : ℕ) : ℝ)) * 3) * Real.log ((p : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hnuR hlogp
    _ = 3 * ((((Nat.log p (2100 * n) : ℕ) : ℝ)) * Real.log ((p : ℕ) : ℝ)) := by
        ring
    _ ≤ 3 * Real.log (((2100 * n : ℕ)) : ℝ) :=
        mul_le_mul_of_nonneg_left hlogLp (by norm_num)

/-- **Counting small-square primes.** Let $n \ge 1$ be a natural number and let $C$ be a finite
set of primes $p$ with $p^2 \le 2100n$. Then $C$ has at most $\sqrt{2100n}/3$ elements. -/
lemma U9_Ccard_le (n : ℕ) (hn : 1 ≤ n) (C : Finset ℕ)
    (hC : ∀ p ∈ C, p.Prime ∧ p ^ 2 ≤ 2100 * n) :
    (C.card : ℝ) ≤ Real.sqrt (((2100 * n : ℕ)) : ℝ) / 3 := by
  have hXnn : (0 : ℝ) ≤ (((2100 * n : ℕ)) : ℝ) := Nat.cast_nonneg _
  have hsub : C ⊆ Nat.primesBelow (⌊Real.sqrt (((2100 * n : ℕ)) : ℝ)⌋₊ + 1) := by
    intro p hp
    obtain ⟨hpp, hsq⟩ := hC p hp
    have hpsq : (((p : ℕ)) : ℝ) ^ 2 ≤ (((2100 * n : ℕ)) : ℝ) := by
      exact_mod_cast hsq
    have hpRnn : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
    have hple : ((p : ℕ) : ℝ) ≤ Real.sqrt (((2100 * n : ℕ)) : ℝ) :=
      (Real.le_sqrt hpRnn hXnn).mpr hpsq
    have hpfloor : p ≤ ⌊Real.sqrt (((2100 * n : ℕ)) : ℝ)⌋₊ := Nat.le_floor hple
    rw [Nat.mem_primesBelow]
    exact ⟨by omega, hpp⟩
  have hcard : C.card ≤ Nat.primeCounting ⌊Real.sqrt (((2100 * n : ℕ)) : ℝ)⌋₊ := by
    have h1 := Finset.card_le_card hsub
    rw [Nat.primesBelow_card_eq_primeCounting'] at h1
    exact h1
  have hXge : (2100 : ℝ) ≤ (((2100 * n : ℕ)) : ℝ) := by
    have h1 : 2100 ≤ 2100 * n := by
      calc (2100 : ℕ) = 2100 * 1 := by ring
        _ ≤ 2100 * n := by gcongr
    exact_mod_cast h1
  have h36 : (36 : ℝ) ≤ Real.sqrt (((2100 * n : ℕ)) : ℝ) := by
    rw [Real.le_sqrt (by norm_num) hXnn]
    have h36sq : (36 : ℝ) ^ 2 = 1296 := by norm_num
    rw [h36sq]
    linarith [hXge]
  have hpi := pi_third h36
  have hcardR : (C.card : ℝ)
      ≤ (Nat.primeCounting ⌊Real.sqrt (((2100 * n : ℕ)) : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast hcard
  linarith [hcardR, hpi]

/-- **Contribution of the small-square primes.** Let $n \ge 1$ be a natural number. For each
divisor $m$ of $210$ put $N_m = 210n/m$, let $\mu$ be the Möbius function, and for a prime $p$
with $p$-adic valuation $v_p$ put
$\nu_9(p, n) = \sum_{m \mid 210} \mu(m) (v_p((10N_m)!) - v_p((9N_m)!) - v_p(N_m!))$. Then the
sum of $\nu_9(p, n) \log p$ over the primes $p \le 1890n$ with $p^2 \le 2100n$ is at most
$\sqrt{2100n} \log(2100n)$. -/
lemma U9_C_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ ((Nat.primesBelow (2100 * n + 1)).filter (fun p => p ≤ 1890 * n)).filter
      (fun p => ¬ 2100 * n < p ^ 2),
      ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
    ≤ Real.sqrt (2100 * (n : ℝ)) * Real.log (2100 * (n : ℝ)) := by
  classical
  set C := ((Nat.primesBelow (2100 * n + 1)).filter (fun p => p ≤ 1890 * n)).filter
    (fun p => ¬ 2100 * n < p ^ 2) with hCdef
  have hCmem : ∀ p ∈ C, p.Prime ∧ p ^ 2 ≤ 2100 * n := by
    intro p hp
    rw [hCdef, Finset.mem_filter] at hp
    obtain ⟨hpT, hnc⟩ := hp
    rw [Finset.mem_filter] at hpT
    obtain ⟨hpS, -⟩ := hpT
    exact ⟨(Nat.mem_primesBelow.mp hpS).2, Nat.not_lt.mp hnc⟩
  have hX1 : (1 : ℝ) ≤ (((2100 * n : ℕ)) : ℝ) := by
    have h1 : 1 ≤ 2100 * n := by omega
    exact_mod_cast h1
  have hterm : ∀ p ∈ C, ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      ≤ 3 * Real.log (((2100 * n : ℕ)) : ℝ) := by
    intro p hp
    obtain ⟨hpp, hsq⟩ := hCmem p hp
    exact U9_Cterm_le n p hn hpp hsq
  have hcard := U9_Ccard_le n hn C hCmem
  have hlogXnn : 0 ≤ Real.log (((2100 * n : ℕ)) : ℝ) := Real.log_nonneg hX1
  have hXeq : (((2100 * n : ℕ)) : ℝ) = 2100 * (n : ℝ) := by simp
  calc ∑ p ∈ C, ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      ≤ ∑ _p ∈ C, 3 * Real.log (((2100 * n : ℕ)) : ℝ) := Finset.sum_le_sum hterm
    _ = (C.card : ℝ) * (3 * Real.log (((2100 * n : ℕ)) : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Real.sqrt (((2100 * n : ℕ)) : ℝ) / 3)
        * (3 * Real.log (((2100 * n : ℕ)) : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard (by linarith [hlogXnn])
    _ = Real.sqrt (2100 * (n : ℝ)) * Real.log (2100 * (n : ℝ)) := by
        rw [hXeq]
        ring

/-- **Upper bound for $\log F_9(n)$ when $(1890n, 2100n]$ has no prime.** Let $n \ge 1$ be a
natural number such that no prime $p$ satisfies $1890n < p \le 2100n$, and let
$\log F_9(n) = \sum_{d \mid 210} \mu(d) \log \frac{(2100n/d)!}{(1890n/d)!\,(210n/d)!}$, where $\mu$
is the Möbius function. Then

$$
\log F_9(n) \le \left(\frac{18900}{279} + \frac{18900}{657} + \frac{18900}{963}\right) n \log 3.4
\;+\; \sqrt{2100n}\,\log(2100n).
$$
-/
theorem logF9_upper (n : ℕ) (hn : 1 ≤ n)
    (hA : ∀ p : ℕ, p.Prime → 1890 * n < p → p ≤ 2100 * n → False) :
    logF9 n ≤ (18900 / 279 + 18900 / 657 + 18900 / 963 : ℝ) * n * Real.log 3.4
      + Real.sqrt (2100 * n) * Real.log (2100 * n) := by
  classical
  rw [U9_bridge n hn]
  have hST : Nat.primesBelow (2100 * n + 1)
      = (Nat.primesBelow (2100 * n + 1)).filter (fun p => p ≤ 1890 * n) := by
    symm
    apply Finset.filter_true_of_mem
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    by_contra hc
    push Not at hc
    exact hA p hp.2 hc (by omega)
  rw [hST]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Nat.primesBelow (2100 * n + 1)).filter (fun p => p ≤ 1890 * n))
    (fun p => 2100 * n < p ^ 2)
    (fun p => ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ))
  have hB := U9_B_le n hn
  have hC := U9_C_le n hn
  rw [← hsplit]
  exact add_le_add hB hC

end MathlibExt.NumberTheory.BreuschWanted.Internal
