/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Rayleigh
public import Mathlib.Data.Set.Card
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Set.Card

/-!
# Counting complementary Beatty terms

For complementary slopes with `1 < α < 2`, the number of β-terms strictly between the
corresponding α- and β-terms is itself a Beatty sequence of slope `2 - α`.
-/

namespace MetaMathlibExt

open Set

/-- **Counting $\beta$-Beatty terms between $\lfloor n\alpha\rfloor$ and $\lfloor n\beta\rfloor$.**
Let $\alpha$ be an irrational number with $1 < \alpha < 2$, let $\beta$ be a real number with
$\alpha^{-1} + \beta^{-1} = 1$, and let $B$ be the set of the numbers $\lfloor k\beta\rfloor$ for
positive integers $k$. Then for every positive integer $n$, the number of elements of $B$ in the
open interval $(\lfloor n\alpha\rfloor, \lfloor n\beta\rfloor)$ equals
$\lfloor n(2 - \alpha)\rfloor$.

By Beatty's theorem, the Beatty sequences of $\alpha$ and $\beta$ are then complementary.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Theorem 3 (`integers-2025-A104-thm-3`). -/
public theorem beatty_card_compl_between_eq_floor {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    ((Ioo (beattySeq α n) (beattySeq β n) ∩ {beattySeq β k | k > 0}).ncard : ℤ) =
      beattySeq (2 - α) n := by
  have hc := Real.holderConjugate_iff.mpr ⟨hα1, hαβ⟩
  have hmono : StrictMono (beattySeq β) := by
    apply strictMono_int_of_lt_succ
    intro k
    simp only [beattySeq, Int.cast_add, Int.cast_one, add_mul, one_mul]
    rw [← Int.add_one_le_iff, ← Int.floor_add_one]
    exact Int.floor_mono (add_le_add_right hc.symm.lt.le _)
  -- The two positive Beatty sequences are disjoint, so the lower endpoint is never a β-term.
  have hpos : beattySeq α n ∈ {j : ℤ | 0 < j} := by
    apply Int.floor_pos.mpr
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hn) hα1.le
  rw [← hirr.beattySeq_symmDiff_beattySeq_pos hc, mem_symmDiff] at hpos
  have cut {k : ℤ} (hk : 0 < k) :
      beattySeq α n < beattySeq β k ↔ beattySeq (α - 1) n < k := by
    have hne : beattySeq α n ≠ beattySeq β k := fun h ↦
      hpos.elim (fun hp ↦ hp.2 ⟨k, hk, h.symm⟩) (fun hp ↦ hp.2 ⟨n, hn, rfl⟩)
    calc
      beattySeq α n < beattySeq β k ↔ (n : ℝ) * α < k * β :=
        ⟨Int.floor_mono.reflect_lt, fun h ↦ (Int.floor_mono h.le).lt_of_ne hne⟩
      _ ↔ beattySeq (α - 1) n < k := by
        rw [← div_lt_iff₀ hc.symm.pos, mul_div_assoc, hc.div_conj_eq_sub_one, beattySeq,
          Int.floor_lt]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcut_nonneg : 0 ≤ beattySeq (α - 1) n :=
    Int.floor_nonneg.mpr (mul_nonneg hnR.le (sub_nonneg.mpr hα1.le))
  have hcut_lt : beattySeq (α - 1) n < n := by
    rw [beattySeq, Int.floor_lt]
    calc
      (n : ℝ) * (α - 1) < (n : ℝ) * 1 := mul_lt_mul_of_pos_left (by linarith) hnR
      _ = _ := mul_one _
  have himage : Ioo (beattySeq α n) (beattySeq β n) ∩ {beattySeq β k | k > 0} =
      beattySeq β '' Ioc (beattySeq (α - 1) n) (n - 1) := by
    ext x
    constructor
    · rintro ⟨⟨hlo, hhi⟩, k, hk, rfl⟩
      exact ⟨k, ⟨(cut hk).mp hlo, by have := hmono.lt_iff_lt.mp hhi; omega⟩, rfl⟩
    · rintro ⟨k, ⟨hlo, hhi⟩, rfl⟩
      have hk := hcut_nonneg.trans_lt hlo
      exact ⟨⟨(cut hk).mpr hlo, hmono (by omega)⟩, k, hk, rfl⟩
  have hbound : beattySeq (α - 1) n ≤ n - 1 := by omega
  rw [himage, ncard_image_of_injective _ hmono.injective, ncard_Ioc,
    Int.card_Ioc_of_le _ _ hbound]
  -- Subtracting a nonintegral number from an integer reverses the strict floor bounds.
  have hfrac : (⌊(n : ℝ) * (α - 1)⌋ : ℝ) < (n : ℝ) * (α - 1) := by
    have hi : Irrational ((n : ℝ) * (α - 1)) := by
      simpa only [Int.cast_one] using (hirr.sub_intCast 1).intCast_mul hn.ne'
    exact (Int.floor_le _).lt_of_ne (hi.ne_int _).symm
  have hnext := Int.lt_floor_add_one ((n : ℝ) * (α - 1))
  symm
  rw [beattySeq, Int.floor_eq_iff]
  simp only [Int.cast_sub, Int.cast_one, beattySeq]
  constructor <;> linarith

end MetaMathlibExt
