/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.Combinatorics.Additive.GDifferenceBases
import Mathlib.Algebra.IsPrimePow
import MathlibExt.Combinatorics.Additive.SingerDifferenceSet

/-!
# Scaling the difference basis number

The Singer difference set modulo `q ^ 2 + q + 1` lifts a minimum basis for `[1, v]` to a basis
for `[1, n]` with at most `(q + 1) * diffBasisNumber g v` elements whenever `n ≤ q ^ 2 * v`.
-/

namespace MetaMathlibExt

namespace diffBasisNumber_le_succ_mul

/-- A basis for a nonempty interval also represents zero with the required multiplicity. -/
private theorem le_subRepCount_zero {B : Finset ℤ} {g : ℕ} (h : g ≤ subRepCount B 1) :
    g ≤ subRepCount B 0 := by
  rw [subRepCount_zero]
  refine h.trans (Finset.card_le_card_of_injOn Prod.snd ?_ ?_)
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp r hr he
    have hp' := (Finset.mem_filter.mp hp).2
    have hr' := (Finset.mem_filter.mp hr).2
    exact Prod.ext (by omega) he

/-- Correcting the two residue representatives gives a quotient between zero and `v`. -/
private theorem exists_quotient {m v : ℕ} [NeZero m] {x : ℤ} (hx : 0 < x)
    (hxv : x ≤ (m : ℤ) * v) {a b : ZMod m} (hab : a - b = (x : ZMod m)) :
    ∃ t : ℤ, 0 ≤ t ∧ t ≤ v ∧ x = a.val - (b.val : ℤ) + m * t := by
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have ha : (a.val : ℤ) < m := by exact_mod_cast a.val_lt
  have hb : (b.val : ℤ) < m := by exact_mod_cast b.val_lt
  have hcast : (((a.val : ℤ) - b.val : ℤ) : ZMod m) = x := by simpa using hab
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcast
  refine ⟨t, ?_, ?_, by omega⟩
  · by_contra! h
    have := mul_le_mul_of_nonneg_left (show t ≤ -1 by omega) hm.le
    omega
  · by_contra! h
    have := mul_le_mul_of_nonneg_left (show (v : ℤ) + 1 ≤ t by omega) hm.le
    rw [mul_add, mul_one] at this
    omega

/-- For fixed residues, lifting each coordinate injects the original representation pairs. -/
private theorem lift_count {m : ℕ} [NeZero m] (D : Finset (ZMod m)) (B : Finset ℤ)
    {a b : ZMod m} (ha : a ∈ D) (hb : b ∈ D) (t : ℤ) :
    subRepCount B t ≤ subRepCount
      ((D ×ˢ B).image fun p => (p.1.val : ℤ) + m * p.2) (a.val - (b.val : ℤ) + m * t) := by
  have hm : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
  apply Finset.card_le_card_of_injOn
    (fun p : ℤ × ℤ => ((a.val : ℤ) + m * p.1, (b.val : ℤ) + m * p.2))
  · intro p hp
    obtain ⟨hpB, hpt⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hpB
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image_of_mem _ (Finset.mk_mem_product ha hp₁)
    · exact Finset.mem_image_of_mem _ (Finset.mk_mem_product hb hp₂)
    · change _ + _ * p.1 - (_ + _ * p.2) = _
      rw [← hpt, mul_sub]
      omega
  · intro p _ r _ h
    exact Prod.ext (mul_left_cancel₀ hm (add_left_cancel (congrArg Prod.fst h)))
      (mul_left_cancel₀ hm (add_left_cancel (congrArg Prod.snd h)))

end diffBasisNumber_le_succ_mul

open diffBasisNumber_le_succ_mul in
/-- **Scaling bound for the $g$-difference basis number.** For natural numbers $g$ and $m$, let
$\eta_g(m)$ be the least size of a finite set $A \subseteq \mathbb{Z}$ such that every
$x \in \{1, \dots, m\}$ is the difference $a - a'$ of at least $g$ ordered pairs
$(a, a') \in A \times A$. If $q$ is a prime and $n$ and $v$ are natural numbers with
$n \le q^2 v$, then $\eta_g(n) \le (q + 1)\,\eta_g(v)$.

For $v \ge 1$ the hypothesis $n \le q^2 v$ says $\sqrt{n/v} \le q$. Corrected reading: the paper
prints the factor $q$, obtained from the misprinted Lemma 4; its proof gives $q + 1$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Corollary 3 (`integers-2025-A77-cor-3`). -/
public theorem diffBasisNumber_le_succ_mul (g q n v : ℕ) (hq : q.Prime)
    (hn : n ≤ q ^ 2 * v) :
    diffBasisNumber g n ≤ (q + 1) * diffBasisNumber g v := by
  by_cases hv : v = 0
  · subst v
    have : n = 0 := by simpa using hn
    subst n
    exact Nat.le_mul_of_pos_left _ (Nat.succ_pos q)
  obtain ⟨B, hcard, hB⟩ := exists_min_basis g v
  let m := q ^ 2 + q + 1
  have : NeZero m := ⟨Nat.succ_ne_zero _⟩
  obtain ⟨D, hD, hSinger⟩ := singer_cyclic_difference_set_exists q hq.isPrimePow
  let F := (D ×ˢ B).image fun p => (p.1.val : ℤ) + m * p.2
  calc
    diffBasisNumber g n ≤ F.card := by
      apply Nat.sInf_le
      refine ⟨F, rfl, fun x hx => ?_⟩
      obtain ⟨hx₁, hxn⟩ := Finset.mem_Icc.mp hx
      have hnv : n ≤ m * v := hn.trans (Nat.mul_le_mul_right v (by dsimp [m]; omega))
      have hxv : x ≤ (m : ℤ) * v := hxn.trans (by exact_mod_cast hnv)
      obtain ⟨a, b, hab⟩ : ∃ a b : D, (a : ZMod m) - b = x := by
        by_cases h : (x : ZMod m) = 0
        · obtain ⟨d, hd⟩ := Finset.card_pos.mp (show 0 < D.card by omega)
          exact ⟨⟨d, hd⟩, ⟨d, hd⟩, by simp [h]⟩
        · obtain ⟨p, hp, _⟩ := hSinger x h
          exact ⟨p.1, p.2, hp⟩
      obtain ⟨t, ht₀, htv, heq⟩ := exists_quotient hx₁ hxv hab
      have ht : g ≤ subRepCount B t := by
        rcases ht₀.eq_or_lt with rfl | ht
        · exact le_subRepCount_zero (hB 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩))
        · exact hB t (Finset.mem_Icc.mpr ⟨ht, htv⟩)
      rw [heq]
      exact ht.trans (lift_count D B a.2 b.2 t)
    _ ≤ (D ×ˢ B).card := Finset.card_image_le
    _ = (q + 1) * diffBasisNumber g v := by rw [Finset.card_product, hD, hcard]

end MetaMathlibExt
