/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Triple ratios of symmetric polynomials on log-concave sequences

The log-concave half of Theorem 3.1 of René Gy, *On Certain Products of Three
Stirling Numbers*, INTEGERS 26 (2026), Article A108.
-/

namespace MetaMathlibExt

open Finset

noncomputable section

-- The two evaluated polynomials and the sum and product of the first `m` terms.
private abbrev E (x : ℕ → ℝ) (m k : ℕ) : ℝ :=
  MvPolynomial.eval (fun i : Fin m => x ((i : ℕ) + 1)) (MvPolynomial.esymm (Fin m) ℝ k)

private abbrev H (x : ℕ → ℝ) (m k : ℕ) : ℝ :=
  MvPolynomial.eval (fun i : Fin m => x ((i : ℕ) + 1)) (MvPolynomial.hsymm (Fin m) ℝ k)

private def S (x : ℕ → ℝ) (m : ℕ) : ℝ := ∑ i ∈ range m, x (i + 1)

private def P (x : ℕ → ℝ) (m : ℕ) : ℝ := ∏ i ∈ range m, x (i + 1)

variable {x : ℕ → ℝ}

private theorem sum_succ (m : ℕ) : S x (m + 1) = S x m + x (m + 1) :=
  sum_range_succ (fun i => x (i + 1)) m

private theorem prod_succ (m : ℕ) : P x (m + 1) = P x m * x (m + 1) :=
  prod_range_succ (fun i => x (i + 1)) m

private theorem e_zero (m : ℕ) : E x m 0 = 1 := by simp [E]

private theorem h_zero (m : ℕ) : H x m 0 = 1 := by simp [H]

private theorem e_one (m : ℕ) : E x m 1 = S x m := by
  simpa [E, S] using (Fin.sum_univ_eq_sum_range (fun i => x (i + 1)) m)

private theorem h_one (m : ℕ) : H x m 1 = S x m := by
  simpa [H, S] using (Fin.sum_univ_eq_sum_range (fun i => x (i + 1)) m)

private theorem e_multiset (m k : ℕ) :
    E x m k = ((range m).val.map (fun i => x (i + 1))).esymm k := by
  have h : (univ : Finset (Fin m)).map Fin.valEmbedding = range m := by
    ext i
    simp only [mem_map, mem_univ, true_and, mem_range]
    exact ⟨fun ⟨a, ha⟩ => ha ▸ a.isLt, fun hi => ⟨⟨i, hi⟩, rfl⟩⟩
  rw [← h]
  simpa only [E, map_val, Multiset.map_map, Function.comp_def, Fin.valEmbedding_apply,
    MvPolynomial.aeval_eq_eval]
    using MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin m) ℝ k
      (fun i : Fin m => x ((i : ℕ) + 1))

-- Separate the squarefree monomials according to whether they use the last variable.
private theorem e_succ (m k : ℕ) :
    E x (m + 1) (k + 1) = E x m (k + 1) + x (m + 1) * E x m k := by
  rw [e_multiset, e_multiset, e_multiset, range_add_one,
    ← cons_eq_insert _ _ notMem_range_self, cons_val]
  simp only [Multiset.map_cons, Multiset.esymm, Multiset.powersetCard_cons,
    Multiset.map_add, Multiset.sum_add, Multiset.map_map, Function.comp_def,
    Multiset.prod_cons, Multiset.sum_map_mul_left]

-- A homogeneous monomial either omits the last variable or has a copy of it to remove.
private theorem h_succ (m k : ℕ) :
    H x (m + 1) (k + 1) = H x m (k + 1) + x (m + 1) * H x (m + 1) k := by
  let e : Fin (m + 1) ≃ Option (Fin m) := finSuccEquivLast
  let w (l d : ℕ) (s : Sym (Fin l) d) :=
    ((s : Multiset (Fin l)).map (fun i : Fin l => x ((i : ℕ) + 1))).prod
  let split : Sym (Fin (m + 1)) (k + 1) ≃
      Sym (Fin (m + 1)) k ⊕ Sym (Fin m) (k + 1) :=
    (Sym.equivCongr e).trans (symOptionSuccEquiv.trans
      (Equiv.sumCongr (Sym.equivCongr e.symm) (Equiv.refl _)))
  simp only [H, MvPolynomial.hsymm, MvPolynomial.eval_sum, map_multiset_prod,
    Multiset.map_map, Function.comp_def, MvPolynomial.eval_X]
  change (∑ s, w (m + 1) (k + 1) s) =
    (∑ s, w m (k + 1) s) + x (m + 1) * ∑ s, w (m + 1) k s
  rw [← split.symm.sum_comp (w (m + 1) (k + 1)), Fintype.sum_sum_type, mul_sum]
  rw [add_comm]
  congr 1
  · apply sum_congr rfl
    intro s _
    change w (m + 1) (k + 1) (Sym.map e.symm (Sym.map some s)) = w m (k + 1) s
    simp [w, Sym.coe_map, Multiset.map_map, e, finSuccEquivLast_symm_some]
  · apply sum_congr rfl
    intro s _
    change w (m + 1) (k + 1) (Sym.map e.symm (Sym.cons none (Sym.map e s))) =
      x (m + 1) * w (m + 1) k s
    simp [w, Sym.map_cons, Sym.map_map, Sym.coe_cons, e]

private theorem e_over (m k : ℕ) (hk : m < k) : E x m k = 0 := by
  rw [e_multiset]
  apply Multiset.esymm_of_card_lt
  simpa using hk

private theorem e_top (m : ℕ) : E x m m = P x m := by
  rw [e_multiset, Multiset.esymm]
  have hc : ((range m).val.map (fun i => x (i + 1))).card = m := by simp
  have ht := Multiset.powersetCard_self ((range m).val.map (fun i => x (i + 1)))
  rw [hc] at ht
  rw [ht]
  simp only [Multiset.map_singleton, Multiset.sum_singleton, P, Finset.prod_map_val]

private theorem h_single (k : ℕ) : H x 1 k = x 1 ^ k := by
  simp [H, MvPolynomial.hsymm, map_multiset_prod, Multiset.map_map, MvPolynomial.eval_X,
    Sym.eq_replicate_of_subsingleton (0 : Fin 1)]

variable (hpos : ∀ k, 1 ≤ k → 0 < x k)

include hpos

private theorem e_pos {m k : ℕ} (hk : k ≤ m) : 0 < E x m k := by
  rw [e_multiset, Finset.esymm_map_val]
  apply sum_pos
  · intro t _
    exact prod_pos fun i _ => hpos (i + 1) (by omega)
  · exact powersetCard_nonempty.mpr (by simpa using hk)

private theorem h_pos {m k : ℕ} (hm : 0 < m) : 0 < H x m k := by
  let i : Fin m := ⟨0, hm⟩
  simp only [H, MvPolynomial.hsymm, MvPolynomial.eval_sum, map_multiset_prod,
    Multiset.map_map, Function.comp_def, MvPolynomial.eval_X]
  apply sum_pos
  · intro s _
    apply Multiset.prod_pos
    intro a ha
    obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp ha
    exact hpos (j + 1) (by omega)
  · exact ⟨Sym.replicate k i, mem_univ _⟩

private theorem sum_pos_prefix {m : ℕ} (hm : 0 < m) : 0 < S x m := by
  rw [← e_one]
  exact e_pos hpos hm

private theorem prod_pos_prefix (m : ℕ) : 0 < P x m :=
  prod_pos fun i _ => hpos (i + 1) (by omega)

variable (hlc : ∀ k, 2 ≤ k → x (k - 1) * x (k + 1) ≤ x k ^ 2)

include hlc

-- Successive ratios are nonincreasing, so adjacent log-concavity compares distant terms.
private theorem strong_step {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    x a * x (b + 1) ≤ x (a + 1) * x b := by
  have hb : 1 ≤ b := ha.trans hab
  rw [mul_comm (x a), ← div_le_div_iff₀ (hpos b hb) (hpos a ha)]
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    apply le_trans _ (ih (ha.trans hab))
    rw [div_le_div_iff₀ (hpos (b + 1) (by omega)) (hpos b (ha.trans hab))]
    simpa [pow_two, mul_comm] using hlc (b + 1) (by omega)

private theorem first_ratio_pow {a : ℕ} (ha : 1 ≤ a) (t : ℕ) :
    x (a + t) * x 1 ^ t ≤ x a * x 2 ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, pow_succ]
    calc
      x (a + (t + 1)) * (x 1 ^ t * x 1) =
          (x 1 * x (a + t + 1)) * x 1 ^ t := by rw [Nat.add_assoc a t 1]; ring
      _ ≤ (x 2 * x (a + t)) * x 1 ^ t :=
        mul_le_mul_of_nonneg_right (strong_step hpos hlc (by decide) (by omega))
          (pow_nonneg (hpos 1 le_rfl).le _)
      _ = x (a + t) * x 1 ^ t * x 2 := by ring
      _ ≤ x a * x 2 ^ t * x 2 := mul_le_mul_of_nonneg_right ih (hpos 2 (by decide)).le
      _ = _ := by ring

omit hlc

private theorem e_near_top (m : ℕ) :
    E x (m + 1) m = P x (m + 1) * S (fun i => (x i)⁻¹) (m + 1) := by
  induction m with
  | zero =>
    simp [e_zero, P, S, (hpos 1 le_rfl).ne']
  | succ m ih =>
    rw [e_succ (m + 1) m, e_top, ih, prod_succ (m + 1),
      sum_succ (x := fun i => (x i)⁻¹) (m + 1)]
    field_simp [(hpos (m + 2) (by omega)).ne']
    ring

private theorem e_two_from_top (m : ℕ) :
    E x (m + 2) m = P x (m + 2) * E (fun i => (x i)⁻¹) (m + 2) 2 := by
  induction m with
  | zero =>
    rw [e_zero, e_succ 1 1, e_over 1 2 (by decide), e_one]
    simp [P, S, prod_range_succ]
    field_simp [(hpos 1 le_rfl).ne', (hpos 2 (by decide)).ne']
  | succ m ih =>
    rw [e_succ (m + 2) m, e_near_top hpos (m + 1), ih, prod_succ (m + 2),
      e_succ (m + 2) 1, e_one]
    field_simp [(hpos (m + 3) (by omega)).ne']
    ring

omit hpos in
private theorem h_empty_succ (k : ℕ) : H x 0 (k + 1) = 0 := by
  have : IsEmpty (Sym (Fin 0) (k + 1)) := ⟨fun s =>
    let ⟨i, _⟩ := s.exists_mem
    Fin.elim0 i⟩
  simp [H, MvPolynomial.hsymm]

omit hpos in
private theorem quadratic_identity (m : ℕ) :
    S x m * S x (m + 1) = E x (m + 1) 2 + H x m 2 := by
  induction m with
  | zero => simp [S, e_over 1 2 (by decide), h_empty_succ 1]
  | succ m ih =>
    rw [e_succ (m + 1) 1, h_succ m 1, e_one, h_one, sum_succ (m + 1)]
    linear_combination ih + S x (m + 1) * sum_succ (x := x) m

-- The degree-two recurrence pairs `x i` in the homogeneous sum with `x (i+1)`
-- in the elementary sum, with the same prefix sum as coefficient.
private theorem quadratic_compare (a b : ℝ) (m : ℕ)
    (h : ∀ i, 1 ≤ i → i ≤ m → b * x i ≤ a * x (i + 1)) :
    b * H x m 2 ≤ a * E x (m + 1) 2 := by
  induction m with
  | zero => simp [h_empty_succ 1, e_over 1 2 (by decide)]
  | succ m ih =>
    rw [h_succ m 1, e_succ (m + 1) 1, h_one, e_one]
    have ht := mul_le_mul_of_nonneg_right (h (m + 1) (by omega) le_rfl)
      (sum_pos_prefix hpos (m := m + 1) (by omega)).le
    linarith only [ih (fun i hi him => h i hi (by omega)), ht]

include hlc

-- The case `n = p = 1`: the two differences reduce to the same degree-two comparison.
private theorem case_np (j : ℕ) :
    E x (j + 2) 2 * S x (j + 1) * S x j ≤
        S x (j + 2) * S x (j + 1) * E x (j + 1) 2 ∧
      S x (j + 2) * S x (j + 1) * H x j 2 ≤
        H x (j + 1) 2 * S x (j + 1) * S x j := by
  have h := quadratic_compare hpos (x (j + 1)) (x (j + 2)) j
    (fun i hi hij => by simpa [mul_comm] using strong_step hpos hlc hi (b := j + 1) (by omega))
  have he : S x (j + 2) * E x (j + 1) 2 - S x j * E x (j + 2) 2 =
      x (j + 1) * E x (j + 1) 2 - x (j + 2) * H x j 2 := by
    rw [e_succ (j + 1) 1, e_one, sum_succ (j + 1)]
    linear_combination E x (j + 1) 2 * sum_succ (x := x) j -
      x (j + 2) * quadratic_identity (x := x) j
  have hh : S x j * H x (j + 1) 2 - S x (j + 2) * H x j 2 =
      x (j + 1) * E x (j + 1) 2 - x (j + 2) * H x j 2 := by
    rw [h_succ j 1, h_one, sum_succ (j + 1)]
    linear_combination x (j + 1) * quadratic_identity (x := x) j -
      H x j 2 * sum_succ (x := x) j
  have hs := (sum_pos_prefix hpos (m := j + 1) (by omega)).le
  have he' : S x j * E x (j + 2) 2 ≤ S x (j + 2) * E x (j + 1) 2 :=
    sub_nonneg.mp (he.symm ▸ sub_nonneg.mpr h)
  have hh' : S x (j + 2) * H x j 2 ≤ S x j * H x (j + 1) 2 :=
    sub_nonneg.mp (hh.symm ▸ sub_nonneg.mpr h)
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left he' hs]
  · nlinarith only [mul_le_mul_of_nonneg_left hh' hs]

-- The case `p = j = 1` on the elementary side uses the complements of the subsets.
private theorem e_case_pj (n : ℕ) :
    E x (n + 2) (n + 1) * E x (n + 1) n * x 1 ≤
      E x (n + 2) n * S x 2 * E x (n + 1) (n + 1) := by
  let y : ℕ → ℝ := fun i => (x i)⁻¹
  have hy : ∀ k, 1 ≤ k → 0 < y k := fun k hk => inv_pos.mpr (hpos k hk)
  have h := quadratic_compare hy (x 2) (x 1) (n + 1) (fun i hi _ => by
    change x 1 * (x i)⁻¹ ≤ x 2 * (x (i + 1))⁻¹
    simpa only [← div_eq_mul_inv, div_le_div_iff₀ (hpos i hi) (hpos (i + 1) (by omega))]
      using strong_step hpos hlc (a := 1) (b := i) le_rfl hi)
  have hS : S x 2 = x 1 + x 2 := by simp [S, sum_range_succ]
  have hc : x 1 * (S y (n + 1) * S y (n + 2)) ≤ S x 2 * E y (n + 2) 2 := by
    rw [quadratic_identity, hS]
    linarith only [h]
  rw [e_near_top hpos (n + 1), e_near_top hpos n, e_two_from_top hpos n, e_top]
  nlinarith only [mul_le_mul_of_nonneg_left hc
    (mul_nonneg (prod_pos_prefix hpos (n + 2)).le (prod_pos_prefix hpos (n + 1)).le)]

-- The case `n = j = 1` on the elementary side uses Gy's shorter induction,
-- after writing the near-top elementary polynomials as sums of reciprocals.
private theorem prefix_inv_compare (m : ℕ) :
    x (m + 2) * S x (m + 1) * S (fun i => (x i)⁻¹) (m + 2) ≤
      x (m + 1) * S x (m + 2) * S (fun i => (x i)⁻¹) (m + 1) := by
  let y : ℕ → ℝ := fun i => (x i)⁻¹
  have hy : ∀ k, 1 ≤ k → 0 < y k := fun k hk => inv_pos.mpr (hpos k hk)
  change x (m + 2) * S x (m + 1) * S y (m + 2) ≤
    x (m + 1) * S x (m + 2) * S y (m + 1)
  have diff (k : ℕ) : x (k + 1) * S x (k + 2) * S y (k + 1) -
        x (k + 2) * S x (k + 1) * S y (k + 2) =
      x (k + 1) * S x (k + 1) * S y k - x (k + 2) * S x k * S y (k + 1) := by
    have ha : x (k + 1) * y (k + 1) = 1 := mul_inv_cancel₀ (hpos _ (by omega)).ne'
    have hb : x (k + 2) * y (k + 2) = 1 := mul_inv_cancel₀ (hpos _ (by omega)).ne'
    rw [sum_succ (x := x) (k + 1), sum_succ (x := y) (k + 1)]
    linear_combination x (k + 1) * S x (k + 1) * sum_succ (x := y) k -
      x (k + 2) * S y (k + 1) * sum_succ (x := x) k + S x (k + 1) * (ha - hb)
  induction m with
  | zero =>
    apply sub_nonneg.mp
    rw [diff]
    simp [S]
  | succ m ih =>
    apply sub_nonneg.mp
    rw [diff, sub_nonneg]
    apply (mul_le_mul_iff_right₀ (hpos (m + 2) (by omega))).mp
    have h₁ := mul_le_mul_of_nonneg_left ih (hpos (m + 3) (by omega)).le
    have h₂ := mul_le_mul_of_nonneg_right (hlc (m + 2) (by omega))
      (mul_nonneg (sum_pos_prefix hpos (m := m + 2) (by omega)).le
        (sum_pos_prefix hy (m := m + 1) (by omega)).le)
    rw [show m + 2 - 1 = m + 1 by omega] at h₂
    nlinarith only [h₁, h₂]

private theorem e_case_nj (p : ℕ) :
    E x (p + 2) (p + 1) * S x (p + 1) * E x p p ≤
      S x (p + 2) * E x (p + 1) p * E x (p + 1) (p + 1) := by
  rw [e_near_top hpos (p + 1), e_near_top hpos p, e_top, e_top]
  have h := prefix_inv_compare hpos hlc p
  -- Use the induction at prefix length `p + 1` and retain the common product of prefixes.
  have hm := mul_le_mul_of_nonneg_left h
    (mul_nonneg (prod_pos_prefix hpos (p + 1)).le (prod_pos_prefix hpos p).le)
  rw [prod_succ (x := x) (p + 1)]
  rw [prod_succ (x := x) p] at hm ⊢
  nlinarith only [hm]

omit hpos hlc in
private theorem h_two_step (k : ℕ) :
    H x 2 (k + 1) = x 1 * H x 2 k + x 2 ^ (k + 1) := by
  induction k with
  | zero => simp [h_one, h_zero, S, sum_range_succ]
  | succ k ih =>
    have h₁ := h_succ (x := x) 1 (k + 1)
    have h₂ := h_succ (x := x) 1 k
    rw [h_single, pow_succ (x 1) (k + 1)] at h₁
    rw [h_single] at h₂
    rw [pow_succ (x 2) (k + 1)]
    linear_combination h₁ + x 2 * ih - x 1 * h₂

omit hpos hlc in
private theorem h_two_sum (k : ℕ) :
    H x 2 k = ∑ b ∈ range (k + 1), x 1 ^ (k - b) * x 2 ^ b := by
  induction k with
  | zero => simp [h_zero]
  | succ k ih =>
    rw [h_two_step, ih, mul_sum, sum_range_succ _ (k + 1)]
    simp only [Nat.sub_self, pow_zero, one_mul]
    congr 1
    refine sum_congr rfl fun b hb => ?_
    rw [show k + 1 - b = k - b + 1 by have := mem_range.mp hb; omega, pow_succ]
    ring

-- The case `n = j = 1` on the homogeneous side is a comparison of power sums.
private theorem h_case_nj (p : ℕ) :
    S x (p + 2) * H x 2 p * H x 1 (p + 1) ≤
      H x 2 (p + 1) * S x (p + 1) * H x 1 p := by
  have ht : x 1 * x (p + 2) * H x 2 p ≤ S x (p + 1) * x 2 ^ (p + 1) := by
    rw [h_two_sum, S, mul_sum, sum_mul]
    apply sum_le_sum
    intro b hb
    have hb' := mem_range.mp hb
    have h := first_ratio_pow hpos hlc (a := b + 1) (by omega) (p - b + 1)
    rw [show b + 1 + (p - b + 1) = p + 2 by omega] at h
    calc
      x 1 * x (p + 2) * (x 1 ^ (p - b) * x 2 ^ b) =
          (x (p + 2) * x 1 ^ (p - b + 1)) * x 2 ^ b := by rw [pow_succ]; ring
      _ ≤ (x (b + 1) * x 2 ^ (p - b + 1)) * x 2 ^ b :=
        mul_le_mul_of_nonneg_right h (pow_nonneg (hpos 2 (by decide)).le _)
      _ = x (b + 1) * x 2 ^ (p + 1) := by
        rw [mul_assoc, ← pow_add, show p - b + 1 + b = p + 1 by omega]
  have hc : S x (p + 2) * H x 2 p * x 1 ≤ H x 2 (p + 1) * S x (p + 1) := by
    rw [sum_succ (p + 1), h_two_step]
    linarith only [ht]
  rw [h_single, h_single, pow_succ]
  nlinarith only [mul_le_mul_of_nonneg_right hc (pow_nonneg (hpos 1 le_rfl).le p)]

-- The case `p = j = 1` on the homogeneous side uses the two scalar recurrences
-- of (3.6): the common inhomogeneous term cancels in each induction step.
private theorem h_case_pj (n : ℕ) :
    H x 3 n * S x 2 * H x 1 (n + 1) ≤
      H x 2 (n + 1) * H x 2 n * S x 1 := by
  let A (k : ℕ) := x 1 * H x 2 (k + 1) * H x 2 k
  let B (k : ℕ) := S x 2 * x 1 ^ (k + 1) * H x 3 k
  let C (k : ℕ) := x 1 * S x 2 * x 1 ^ (k + 1) * H x 2 (k + 1)
  have s₂ : S x 2 = x 1 + x 2 := by simp [S, sum_range_succ]
  have ha (k : ℕ) : A (k + 1) = x 2 ^ 2 * A k + C k := by
    have h₁ := h_succ (x := x) 1 (k + 1)
    have h₂ := h_succ (x := x) 1 k
    rw [h_single, pow_succ (x 1) (k + 1)] at h₁
    rw [h_single] at h₂
    dsimp only [A, C]
    rw [s₂]
    linear_combination x 1 * H x 2 (k + 1) * (h₁ + x 2 * h₂)
  have hb (k : ℕ) : B (k + 1) = (x 1 * x 3) * B k + C k := by
    dsimp only [B, C]
    rw [h_succ 2 k, pow_succ (x 1) (k + 1)]
    ring
  have hc (k : ℕ) : B k ≤ A k := by
    induction k with
    | zero => simp [A, B, h_zero, h_one, mul_comm]
    | succ k ih =>
      have hB : 0 ≤ B k := mul_nonneg
        (mul_nonneg (sum_pos_prefix hpos (m := 2) (by decide)).le
          (pow_nonneg (hpos 1 le_rfl).le _))
        (h_pos hpos (m := 3) (by decide)).le
      rw [ha, hb]
      exact add_le_add ((mul_le_mul_of_nonneg_right (hlc 2 (by decide)) hB).trans
        (mul_le_mul_of_nonneg_left ih (sq_nonneg _))) le_rfl
  rw [h_single, show S x 1 = x 1 by simp [S]]
  linarith only [hc n]

omit hpos hlc in
private theorem le_mul_ratios {a b c d e f : ℝ} (hb : 0 < b) (hd : 0 < d) (hf : 0 < f) :
    a / b ≤ c / d * (e / f) ↔ a * d * f ≤ c * e * b := by
  rw [div_mul_div_comm, div_le_div_iff₀ hb (mul_pos hd hf), mul_assoc a]

omit hpos hlc in
private theorem mul_ratios_le {a b c d e f : ℝ} (hb : 0 < b) (hd : 0 < d) (hf : 0 < f) :
    a / b * (c / d) ≤ e / f ↔ a * c * f ≤ e * b * d := by
  rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hb hd) hf, mul_assoc e]

omit hpos hlc

/-- **Gy's triple-ratio inequalities for log-concave sequences.** Let $n$, $p$ and $j$ be
positive integers, at least two of which equal $1$, and let $x_1, x_2, \dots$ be positive reals
with $x_{k-1} x_{k+1} \le x_k^2$ for all $k \ge 2$. For $m \ge 0$ write $e_i(m)$ and $h_i(m)$ for
the elementary and the complete homogeneous symmetric polynomials of degree $i$ evaluated at
$(x_1, \dots, x_m)$, and put $N = n + p + j$. Then
$$\frac{e_{n+p}(N)}{e_{n+p}(N-1)} \le \frac{e_n(N)}{e_n(N-1)} \cdot \frac{e_p(p+j)}{e_p(p+j-1)}$$
and
$$\frac{h_n(p+j+1)}{h_n(p+j)} \cdot \frac{h_p(j+1)}{h_p(j)} \le \frac{h_{n+p}(j+1)}{h_{n+p}(j)}.$$

Source: René Gy, *On Certain Products of Three Stirling Numbers*, INTEGERS 26 (2026),
Article A108, Theorem 3.1 (`integers-2026-A108-thm-3-1`). -/
public theorem symm_triple_ratio_of_logConcave (x : ℕ → ℝ)
    (hpos : ∀ k, 1 ≤ k → 0 < x k) (hlc : ∀ k, 2 ≤ k → x (k - 1) * x (k + 1) ≤ x k ^ 2)
    {n p j : ℕ} (hn : 0 < n) (hp : 0 < p) (hj : 0 < j)
    (h11 : (n = 1 ∧ p = 1) ∨ (n = 1 ∧ j = 1) ∨ (p = 1 ∧ j = 1)) :
    MvPolynomial.eval (fun i : Fin (n + p + j) => x ((i : ℕ) + 1))
          (MvPolynomial.esymm (Fin (n + p + j)) ℝ (n + p)) /
        MvPolynomial.eval (fun i : Fin (n + p + j - 1) => x ((i : ℕ) + 1))
          (MvPolynomial.esymm (Fin (n + p + j - 1)) ℝ (n + p)) ≤
      MvPolynomial.eval (fun i : Fin (n + p + j) => x ((i : ℕ) + 1))
            (MvPolynomial.esymm (Fin (n + p + j)) ℝ n) /
          MvPolynomial.eval (fun i : Fin (n + p + j - 1) => x ((i : ℕ) + 1))
            (MvPolynomial.esymm (Fin (n + p + j - 1)) ℝ n) *
        (MvPolynomial.eval (fun i : Fin (p + j) => x ((i : ℕ) + 1))
            (MvPolynomial.esymm (Fin (p + j)) ℝ p) /
          MvPolynomial.eval (fun i : Fin (p + j - 1) => x ((i : ℕ) + 1))
            (MvPolynomial.esymm (Fin (p + j - 1)) ℝ p)) ∧
    MvPolynomial.eval (fun i : Fin (p + j + 1) => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin (p + j + 1)) ℝ n) /
        MvPolynomial.eval (fun i : Fin (p + j) => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin (p + j)) ℝ n) *
      (MvPolynomial.eval (fun i : Fin (j + 1) => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin (j + 1)) ℝ p) /
        MvPolynomial.eval (fun i : Fin j => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin j) ℝ p)) ≤
      MvPolynomial.eval (fun i : Fin (j + 1) => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin (j + 1)) ℝ (n + p)) /
        MvPolynomial.eval (fun i : Fin j => x ((i : ℕ) + 1))
          (MvPolynomial.hsymm (Fin j) ℝ (n + p)) := by
  change E x (n + p + j) (n + p) / E x (n + p + j - 1) (n + p) ≤
      E x (n + p + j) n / E x (n + p + j - 1) n * (E x (p + j) p / E x (p + j - 1) p) ∧
    H x (p + j + 1) n / H x (p + j) n * (H x (j + 1) p / H x j p) ≤
      H x (j + 1) (n + p) / H x j (n + p)
  rw [le_mul_ratios (e_pos hpos (by omega)) (e_pos hpos (by omega)) (e_pos hpos (by omega)),
    mul_ratios_le (h_pos hpos (by omega)) (h_pos hpos hj) (h_pos hpos hj)]
  rcases h11 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa only [Nat.add_comm 2 j, Nat.add_comm 1 j, Nat.add_sub_cancel,
      show j + 2 - 1 = j + 1 by omega, e_one, h_one] using case_np hpos hlc j
  · simpa only [Nat.add_comm 1 p, Nat.add_sub_cancel, e_one, h_one]
      using And.intro (e_case_nj hpos hlc p) (h_case_nj hpos hlc p)
  · simpa only [Nat.add_sub_cancel, e_one, h_one, show S x 1 = x 1 by simp [S]]
      using And.intro (e_case_pj hpos hlc n) (h_case_pj hpos hlc n)

end

end MetaMathlibExt
