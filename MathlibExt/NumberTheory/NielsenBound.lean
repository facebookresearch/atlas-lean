/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nielsen's bound

The first crossing of a rational threshold by a product of factors `1 - 1 / x` bounds
the product of the ordered denominators.
-/

namespace MetaMathlibExt
namespace nielsen_prod_one_sub_inv_bound

open Finset

private abbrev prefixProd {α : Type*} [CommMonoid α] (f : ℕ → α) (n : ℕ) :=
  ∏ i ∈ range n, f i

private abbrev baseProd (x : ℕ → ℕ) (k : ℕ) : ℕ := prefixProd x k

private abbrev factor (x : ℕ) : ℚ := 1 - 1 / (x : ℚ)

private theorem factor_pos {x : ℕ} (hx : 1 < x) : 0 < factor x := by
  have h : (1 : ℚ) < x := by exact_mod_cast hx
  exact sub_pos.mpr ((div_lt_one (by positivity)).mpr h)

-- Bernoulli's inequality gives a one-factor comparison with exponent x - 1.
private theorem factor_ratio {x y : ℕ} (hx : 1 < x) (hy : 1 < y) :
    (x : ℚ) / y ≤ (factor x / factor y) ^ (x - 1) := by
  have hx' : (1 : ℚ) < x := by exact_mod_cast hx
  have hy' : (1 : ℚ) < y := by exact_mod_cast hy
  have h := one_add_mul_sub_le_pow (a := factor x / factor y)
    (by have := div_pos (factor_pos hx) (factor_pos hy); linarith) (x - 1)
  refine le_trans ?_ h
  rw [Nat.cast_sub (by omega : 1 ≤ x), Nat.cast_one]
  unfold factor
  field_simp [show (0 : ℚ) < x by linarith, show (0 : ℚ) < y by linarith,
    show (0 : ℚ) < y - 1 by linarith]
  nlinarith [sq_nonneg ((x : ℚ) - y)]

-- At each proper prefix the factor ratio is at least one, so monotonicity of x
-- lets us raise its exponent to that of the next term before applying factor_ratio.
private theorem compare_prefix (x y : ℕ → ℕ) (hx : ∀ i, 1 < x i) (hy : ∀ i, 1 < y i)
    (hmono : Monotone x) (n : ℕ) (hp : ∀ k < n, baseProd y k ≤ baseProd x k) :
    (baseProd x n : ℚ) / baseProd y n ≤
      (prefixProd (fun i => factor (x i)) n / prefixProd (fun i => factor (y i)) n) ^
        (x (n - 1) - 1) := by
  induction n with
  | zero => simp [baseProd, prefixProd]
  | succ n ih =>
    have Y : 0 < (baseProd y n : ℚ) := by
      exact_mod_cast prod_pos (fun i _ => (hy i).trans' Nat.zero_lt_one)
    have FX := prod_pos (s := range n) (fun i _ => factor_pos (hx i))
    have FY := prod_pos (s := range n) (fun i _ => factor_pos (hy i))
    let q := prefixProd (fun i => factor (x i)) n / prefixProd (fun i => factor (y i)) n
    have hprev : (baseProd x n : ℚ) / baseProd y n ≤ q ^ (x (n - 1) - 1) :=
      ih fun k hk => hp k (by omega)
    have hq : 1 ≤ q := by
      have hpow := ((one_le_div Y).2 (by exact_mod_cast hp n (by omega))).trans hprev
      by_contra! hlt
      exact (pow_lt_one₀ (div_pos FX FY).le hlt (by have := hx (n - 1); omega)).not_ge hpow
    have hexp := Nat.sub_le_sub_right (hmono (Nat.sub_le n 1)) 1
    have step := mul_le_mul (hprev.trans (pow_le_pow_right₀ hq hexp))
      (factor_ratio (hx n) (hy n)) (by positivity) (by positivity)
    simpa only [baseProd, prefixProd, prod_range_succ, Nat.cast_mul, Nat.add_one_sub_one, q,
      mul_div_mul_comm, mul_pow] using step

private abbrev scale (a k : ℕ) := (a + 1) ^ 2 ^ k

private theorem scale_succ (a k : ℕ) : scale a (k + 1) = scale a k ^ 2 := by
  rw [scale, pow_succ 2, pow_mul]

private abbrev model (a n i : ℕ) := if i = n then scale a i else scale a i + 1

-- Before the last term, both products telescope by (t - 1)(t + 1) = t² - 1.
private theorem model_prefix (a n k : ℕ) (hk : k ≤ n) :
    a * baseProd (model a n) k + 1 = scale a k ∧
    (a + 1) * baseProd (fun i => model a n i - 1) k = scale a k := by
  induction k with
  | zero => simp [scale, baseProd, prefixProd]
  | succ k ih =>
    obtain ⟨h₁, h₂⟩ := ih (by omega)
    simp only [baseProd, prefixProd, prod_range_succ, model, ite_eq_right (by omega : k ≠ n),
      Nat.add_one_sub_one, scale_succ]
    constructor
    · change a * (baseProd (model a n) k * (scale a k + 1)) + 1 = _
      rw [← h₁]
      ring
    · change (a + 1) * (baseProd (fun i => model a n i - 1) k * scale a k) = _
      rw [← mul_assoc, h₂, pow_two]

private abbrev preds (x : ℕ → ℕ) := fun i => x i - 1

private theorem factor_product (x : ℕ → ℕ) (hx : ∀ i, 1 < x i) (k : ℕ) :
    prefixProd (fun i => factor (x i)) k = (baseProd (preds x) k : ℚ) / baseProd x k := by
  simp only [baseProd, prefixProd, Nat.cast_prod, ← prod_div_distrib]
  refine prod_congr rfl fun i _ => ?_
  have hxi : 0 < (x i : ℚ) := by exact_mod_cast (hx i).trans' Nat.zero_lt_one
  simp [factor, preds, Nat.cast_sub (by have := hx i; omega : 1 ≤ x i), sub_div, hxi.ne']

private theorem bases_pos (x : ℕ → ℕ) (hx : ∀ i, 1 < x i) (k : ℕ) :
    0 < baseProd x k := prod_pos fun i _ => (hx i).trans' Nat.zero_lt_one

-- If none of the proper prefixes is small, comparison with the model forces
-- the full product to be at most the model's full product.
private theorem bound_of_large_prefixes (x : ℕ → ℕ) (hx : ∀ i, 1 < x i)
    (hmono : Monotone x) (a b n : ℕ) (ha : 0 < a) (hab : a < b)
    (hlow : b * baseProd (preds x) (n + 1) ≤ a * baseProd x (n + 1))
    (hlarge : ∀ k, 0 < k → k ≤ n → scale a k ≤ a * baseProd x k) :
    a * baseProd x (n + 1) ≤ scale a n * (scale a n - 1) := by
  let y := model a n
  have hy : ∀ i, 1 < y i := by
    intro i
    have hs : 1 < scale a i := one_lt_pow₀ (by omega) (by positivity)
    dsimp [y, model]
    split <;> omega
  have hp : ∀ k < n + 1, baseProd y k ≤ baseProd x k := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp [baseProd, prefixProd]
    · have h := (model_prefix a n k (by omega)).1
      have h' := hlarge k hpos (by omega)
      exact Nat.le_of_mul_le_mul_left (by dsimp [y]; omega) ha
  obtain ⟨h₁, h₂⟩ := model_prefix a n n le_rfl
  have hlast : y n = scale a n := by simp [y, model]
  have hprod : a * baseProd y (n + 1) = scale a n * (scale a n - 1) := by
    rw [show baseProd y (n + 1) = baseProd y n * y n from prod_range_succ ..,
      ← mul_assoc, hlast, mul_comm]
    congr 1
    dsimp [y]
    omega
  have hequal : (a + 1) * baseProd (preds y) (n + 1) = a * baseProd y (n + 1) := by
    rw [hprod, show baseProd (preds y) (n + 1) = baseProd (preds y) n * (y n - 1) from
      prod_range_succ .., ← mul_assoc, hlast]
    exact congrArg (· * (scale a n - 1)) h₂
  have hfx : prefixProd (fun i => factor (x i)) (n + 1) ≤ (a : ℚ) / (a + 1) := by
    rw [factor_product x hx, div_le_div_iff₀ (by exact_mod_cast bases_pos x hx _) (by positivity)]
    exact_mod_cast (mul_comm _ _).le.trans ((Nat.mul_le_mul_right _ hab).trans hlow)
  have hfy : prefixProd (fun i => factor (y i)) (n + 1) = (a : ℚ) / (a + 1) := by
    rw [factor_product y hy, div_eq_div_iff (by exact_mod_cast (bases_pos y hy _).ne')
      (by positivity)]
    exact_mod_cast (mul_comm _ _).trans hequal
  have hcomp := compare_prefix x y hx hy hmono (n + 1) hp
  have hpos := prod_pos (s := range (n + 1)) (fun i _ => factor_pos (hy i))
  have hnonneg := prod_pos (s := range (n + 1)) (fun i _ => factor_pos (hx i))
  have hle := pow_le_one₀ (n := x (n + 1 - 1) - 1) (div_nonneg hnonneg.le hpos.le)
    ((div_le_one hpos).2 (hfx.trans_eq hfy.symm))
  have hxy := (div_le_one (by exact_mod_cast bases_pos y hy _)).1 (hcomp.trans hle)
  rw [← hprod]
  exact Nat.mul_le_mul_left a (by exact_mod_cast hxy)

-- Split off any small proper prefix and absorb its products into the threshold.
private theorem bound (n a b : ℕ) (x : ℕ → ℕ) (hx : ∀ i, 1 < x i) (hmono : Monotone x)
    (ha : 0 < a) (hlow : b * baseProd (preds x) (n + 1) ≤ a * baseProd x (n + 1))
    (hup : a * baseProd x n < b * baseProd (preds x) n) :
    a * baseProd x (n + 1) ≤ scale a n * (scale a n - 1) := by
  induction n using Nat.strong_induction_on generalizing a b x with
  | ind n ih =>
    by_cases hsmall : ∃ k, 0 < k ∧ k ≤ n ∧ a * baseProd x k < scale a k
    · obtain ⟨k, hk, hkn, hsize⟩ := hsmall
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
      let tail := fun i => x (k + i)
      let a' := a * baseProd x k
      let b' := b * baseProd (preds x) k
      have splitX (l : ℕ) : baseProd x (k + l) = baseProd x k * baseProd tail l := prod_range_add ..
      have splitY (l : ℕ) :
          baseProd (preds x) (k + l) = baseProd (preds x) k * baseProd (preds tail) l :=
        prod_range_add ..
      rw [Nat.add_assoc, splitY, splitX, ← mul_assoc, ← mul_assoc] at hlow
      rw [splitX, splitY, ← mul_assoc, ← mul_assoc] at hup
      have h := ih m (by omega) a' b' tail (fun i => hx (k + i))
        (fun i j hij => hmono (Nat.add_le_add_left hij k)) (Nat.mul_pos ha (bases_pos x hx k))
        hlow hup
      have hscale : scale a' m ≤ scale a (k + m) := by
        rw [scale, scale, pow_add, pow_mul]
        exact Nat.pow_le_pow_left hsize _
      rw [Nat.add_assoc, splitX, ← mul_assoc]
      exact h.trans (Nat.mul_le_mul hscale (Nat.sub_le_sub_right hscale 1))
    · have hle : baseProd (preds x) n ≤ baseProd x n :=
        prod_le_prod fun i _ => Nat.sub_le (x i) 1
      have hab : a < b := by
        by_contra! h
        exact hup.not_ge (Nat.mul_le_mul h hle)
      exact bound_of_large_prefixes x hx hmono a b n ha hab hlow
        (fun k hk hkn => le_of_not_gt fun h => hsmall ⟨k, hk, hkn, h⟩)

end nielsen_prod_one_sub_inv_bound

open nielsen_prod_one_sub_inv_bound Finset

/-- **Nielsen's bound.** Let $r$, $a$ and $b$ be natural numbers and let $x_1 \le \dots \le x_r$ be
integers with every $x_j > 1$. If
$\prod_{j=1}^{r} (1 - 1/x_j) \le a/b < \prod_{j=1}^{r-1} (1 - 1/x_j)$, then
$a \prod_{j=1}^{r} x_j \le (a + 1)^{2^r} - (a + 1)^{2^{r-1}}$.

The paper assumes $r$, $a$ and $b$ positive; this follows from the hypotheses, since the left-hand
product is positive (so $a > 0$ and $b > 0$, reading $a/0$ as $0$) and both products equal $1$
when $r = 0$.

Source: Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26 (2026),
Article A100, Lemma 1 (`integers-2026-A100-lem-1`), citing P. Nielsen, Math. Comp. 84 (2015),
Lemma 1.4. -/
public theorem nielsen_prod_one_sub_inv_bound (r a b : ℕ) (x : Fin r → ℕ)
    (hmono : Monotone x) (hx : ∀ j, 1 < x j)
    (hlow : ∏ j, (1 - 1 / (x j : ℚ)) ≤ (a : ℚ) / b)
    (hup : (a : ℚ) / b <
      ∏ j ∈ Finset.univ.filter (fun j : Fin r => j.val + 1 < r), (1 - 1 / (x j : ℚ))) :
    a * ∏ j, x j ≤ (a + 1) ^ 2 ^ r - (a + 1) ^ 2 ^ (r - 1) := by
  cases r with
  | zero =>
    simp only [univ_eq_empty, filter_empty, prod_empty] at hlow hup
    exact (hup.not_ge hlow).elim
  | succ n =>
    let z (i : ℕ) := x ⟨min i n, by omega⟩
    have hz : ∀ i, 1 < z i := fun i => hx _
    have hzm : Monotone z := fun _ _ hij => hmono (Fin.mk_le_mk.mpr (min_le_min_right n hij))
    have hfin (i : Fin (n + 1)) : z i = x i := by
      dsimp [z]
      congr 1
      exact Fin.ext (min_eq_left (by omega : i.val ≤ n))
    have hfull : (∏ i, x i) = baseProd z (n + 1) := by
      simpa only [baseProd, prefixProd, hfin] using Fin.prod_univ_eq_prod_range z (n + 1)
    have hfac : (∏ i, factor (x i)) = prefixProd (fun i => factor (z i)) (n + 1) := by
      simpa only [prefixProd, hfin] using
        Fin.prod_univ_eq_prod_range (fun i => factor (z i)) (n + 1)
    have hpre : (∏ i ∈ univ.filter (fun i : Fin (n + 1) => i.val + 1 < n + 1),
        factor (x i)) = prefixProd (fun i => factor (z i)) n := by
      rw [prod_filter, Fin.prod_univ_castSucc]
      simp only [Fin.val_last, lt_self_iff_false, ite_false, mul_one, Fin.val_castSucc]
      rw [prefixProd, ← Fin.prod_univ_eq_prod_range (fun i => factor (z i)) n]
      exact prod_congr rfl fun i _ => by simp [show i.val + 1 < n + 1 by omega, ← hfin i.castSucc]
    change (∏ i, factor (x i)) ≤ _ at hlow
    change _ < ∏ i ∈ _, factor (x i) at hup
    rw [hfac, factor_product z hz] at hlow
    rw [hpre, factor_product z hz] at hup
    have hpos (k : ℕ) : (0 : ℚ) < baseProd z k := by exact_mod_cast bases_pos z hz k
    have hpred : 0 < baseProd (preds z) (n + 1) :=
      prod_pos fun i _ => Nat.sub_pos_of_lt (hz i)
    have hab := (div_pos (by exact_mod_cast hpred) (hpos _)).trans_le hlow
    have ha : 0 < a := by
      by_contra! h
      simp [Nat.eq_zero_of_le_zero h] at hab
    have hb : (0 : ℚ) < b := by
      by_contra! h
      have : (b : ℚ) = 0 := le_antisymm h (by positivity)
      simp [this] at hab
    have h₁ := (div_le_div_iff₀ (hpos _) hb).mp hlow
    have h₂ := (div_lt_div_iff₀ hb (hpos _)).mp hup
    have h := bound n a b z hz hzm ha
      (by rw [mul_comm b]; exact_mod_cast h₁) (by rw [mul_comm b]; exact_mod_cast h₂)
    rw [hfull, Nat.add_one_sub_one,
      show (a + 1) ^ 2 ^ (n + 1) = scale a n ^ 2 from scale_succ a n]
    simpa [Nat.mul_sub, pow_two] using h

end MetaMathlibExt
