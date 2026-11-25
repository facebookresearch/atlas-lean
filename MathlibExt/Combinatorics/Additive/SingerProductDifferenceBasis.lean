/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import MathlibExt.Combinatorics.Additive.GDifferenceBases

/-!
# Singer product construction of difference bases

A Singer difference set modulo `q ^ 2 + q + 1` lifts a difference basis for `[1, v]`
to one for `[1, (q ^ 2 + q + 1) * v]` without reducing the representation multiplicity.
-/

namespace MetaMathlibExt

/-- **Singer product construction of difference bases.** Let $g, q, v \in \mathbb{N}$ and
$m = q^2 + q + 1$. Let $a_0, \dots, a_q$ be integers in $\{1, \dots, m\}$ such that every
$r \in \{1, \dots, m - 1\}$ is congruent modulo $m$ to $a_i - a_j$ for exactly one ordered pair
$(i, j)$ with $i \ne j$ (a Singer difference set modulo $m$). Let $B$ be a finite set of
integers such that every $x \in \{1, \dots, v\}$ equals $b - b'$ for at least $g$ ordered pairs
$(b, b') \in B \times B$. Then, with $F = \{a_i + mb : 0 \le i \le q,\ b \in B\}$, every
$s \in \{1, \dots, mv\}$ equals $f - f'$ for at least $g$ ordered pairs $(f, f') \in F \times F$.

All $q + 1$ Singer elements are used; the paper prints $1 \le i \le q$, for which the statement
fails.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 4 (`integers-2025-A77-lem-4`). -/
public theorem singer_product_diffBasis (g q v : ℕ) (a : Fin (q + 1) → ℤ)
    (ha : ∀ i, a i ∈ Finset.Icc (1 : ℤ) (q ^ 2 + q + 1))
    (hsinger : ∀ r ∈ Finset.Icc (1 : ℤ) (q ^ 2 + q),
      ∃! ij : Fin (q + 1) × Fin (q + 1),
        ij.1 ≠ ij.2 ∧ a ij.1 - a ij.2 ≡ r [ZMOD (q ^ 2 + q + 1 : ℤ)])
    (B : Finset ℤ) (hB : ∀ x ∈ Finset.Icc (1 : ℤ) v, g ≤ subRepCount B x) :
    ∀ s ∈ Finset.Icc (1 : ℤ) ((q ^ 2 + q + 1) * v),
      g ≤ subRepCount
        ((Finset.univ ×ˢ B).image fun ib : Fin (q + 1) × ℤ =>
          a ib.1 + (q ^ 2 + q + 1) * ib.2) s := by
  intro s hs
  let m : ℤ := (q : ℤ) ^ 2 + q + 1
  let f : Fin (q + 1) × ℤ → ℤ := fun p => a p.1 + m * p.2
  change s ∈ Finset.Icc 1 (m * v) at hs
  change g ≤ subRepCount ((Finset.univ ×ˢ B).image f) s
  have hm : 0 < m := by dsimp [m]; positivity
  obtain ⟨hs₁, hsv⟩ := Finset.mem_Icc.mp hs
  obtain ⟨i, j, hij⟩ : ∃ i j, a i - a j ≡ s [ZMOD m] := by
    by_cases hr : s % m = 0
    · exact ⟨0, 0, by simpa only [sub_self, hr] using Int.mod_modEq s m⟩
    · have hlow := Int.emod_nonneg s hm.ne'
      have hupp : s % m < (q : ℤ) ^ 2 + q + 1 := Int.emod_lt_of_pos s hm
      have hmem : s % m ∈ Finset.Icc 1 ((q : ℤ) ^ 2 + q) :=
        Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      obtain ⟨p, hp, _⟩ := hsinger _ hmem
      exact ⟨p.1, p.2, hp.2.trans (Int.mod_modEq s m)⟩
  obtain ⟨t, heq⟩ := Int.modEq_iff_add_fac.mp hij
  have hi : 1 ≤ a i ∧ a i ≤ m := Finset.mem_Icc.mp (ha i)
  have hj : 1 ≤ a j ∧ a j ≤ m := Finset.mem_Icc.mp (ha j)
  -- The representative difference lies strictly between `-m` and `m`.
  have ht₀ : 0 ≤ t := by
    by_contra! h
    have hmul := mul_le_mul_of_nonneg_left (show t ≤ -1 by omega) hm.le
    rw [mul_neg_one] at hmul
    omega
  have htv : t ≤ (v : ℤ) := by
    by_contra! h
    have hmul := mul_le_mul_of_nonneg_left (show (v : ℤ) + 1 ≤ t by omega) hm.le
    rw [mul_add, mul_one] at hmul
    omega
  have hcount : g ≤ subRepCount B t := by
    rcases ht₀.eq_or_lt with rfl | ht
    · have hv : 1 ≤ (v : ℤ) := by
        by_contra! h
        have hv : v = 0 := by omega
        simp [hv] at hsv
        omega
      -- Distinct representations of 1 have distinct second coordinates.
      rw [subRepCount_zero]
      refine (hB 1 (Finset.mem_Icc.mpr ⟨le_rfl, hv⟩)).trans
        (Finset.card_le_card_of_injOn Prod.snd ?_ ?_)
      · intro p hp
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
      · intro p hp p' hp' h
        have hp₁ := (Finset.mem_filter.mp hp).2
        have hp₂ := (Finset.mem_filter.mp hp').2
        exact Prod.ext (by omega) h
    · exact hB t (Finset.mem_Icc.mpr ⟨ht, htv⟩)
  -- For the fixed indices, lift each ordered representation from `B` into the image.
  have hinj (k : Fin (q + 1)) : Function.Injective (fun b : ℤ => f (k, b)) :=
    fun _ _ h => mul_left_cancel₀ hm.ne' (add_left_cancel h)
  refine hcount.trans (Finset.card_le_card_of_injOn
    (fun p : ℤ × ℤ => (f (i, p.1), f (j, p.2))) ?_ ?_)
  · intro p hp
    obtain ⟨hpB, hpt⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hpB
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image_of_mem f (Finset.mk_mem_product (Finset.mem_univ i) hp₁)
    · exact Finset.mem_image_of_mem f (Finset.mk_mem_product (Finset.mem_univ j) hp₂)
    · change a i + m * p.1 - (a j + m * p.2) = s
      rw [heq, ← hpt, mul_sub]
      omega
  · intro p _ p' _ h
    exact Prod.ext (hinj i (congrArg Prod.fst h)) (hinj j (congrArg Prod.snd h))

end MetaMathlibExt
