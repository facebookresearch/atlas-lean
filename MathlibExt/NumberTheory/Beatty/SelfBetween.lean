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
# Counting terms between complementary Beatty sequences

For complementary slopes with `1 < α < 2`, the number of α-terms strictly between the
corresponding α- and β-terms is itself a Beatty sequence of slope `β - 2`.
-/

namespace MetaMathlibExt

open Set

/-- **Counting $\alpha$-Beatty terms between $\lfloor n\alpha\rfloor$ and $\lfloor n\beta\rfloor$.**
Let $\alpha$ be an irrational number with $1 < \alpha < 2$, let $\beta$ be a real number with
$\alpha^{-1} + \beta^{-1} = 1$, and let $A$ be the set of the numbers $\lfloor k\alpha\rfloor$ for
positive integers $k$. Then for every positive integer $n$, the number of elements of $A$ in the
open interval $(\lfloor n\alpha\rfloor, \lfloor n\beta\rfloor)$ equals
$\lfloor n(\beta - 2)\rfloor$.

By Beatty's theorem, the Beatty sequences of $\alpha$ and $\beta$ are then complementary.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Theorem 4 (`integers-2025-A104-thm-4`). -/
public theorem beatty_card_self_between_eq_floor {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    ((Ioo (beattySeq α n) (beattySeq β n) ∩ {beattySeq α k | k > 0}).ncard : ℤ) =
      beattySeq (β - 2) n := by
  have hc := Real.holderConjugate_iff.mpr ⟨hα1, hαβ⟩
  have hmono : StrictMono (beattySeq α) := by
    apply strictMono_int_of_lt_succ
    intro k
    simp only [beattySeq, Int.cast_add, Int.cast_one, add_mul, one_mul]
    rw [← Int.add_one_le_iff, ← Int.floor_add_one]
    exact Int.floor_mono (add_le_add_right hα1.le _)
  -- Complementarity excludes equality at the upper endpoint, even after taking floors.
  have hpos : beattySeq β n ∈ {j : ℤ | 0 < j} := by
    apply Int.floor_pos.mpr
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hn) hc.symm.lt.le
  rw [← hirr.beattySeq_symmDiff_beattySeq_pos hc, mem_symmDiff] at hpos
  have cut {k : ℤ} (hk : 0 < k) :
      beattySeq α k < beattySeq β n ↔ k ≤ beattySeq (β - 1) n := by
    have hne : beattySeq α k ≠ beattySeq β n := fun h ↦
      hpos.elim (fun hp ↦ hp.2 ⟨n, hn, rfl⟩) (fun hp ↦ hp.2 ⟨k, hk, h⟩)
    calc
      beattySeq α k < beattySeq β n ↔ (k : ℝ) * α ≤ n * β :=
        ⟨fun h ↦ (Int.floor_mono.reflect_lt h).le, fun h ↦ (Int.floor_mono h).lt_of_ne hne⟩
      _ ↔ k ≤ beattySeq (β - 1) n := by
        rw [← le_div_iff₀ hc.pos, mul_div_assoc, hc.symm.div_conj_eq_sub_one, beattySeq,
          Int.le_floor]
  have himage : Ioo (beattySeq α n) (beattySeq β n) ∩ {beattySeq α k | k > 0} =
      beattySeq α '' Ioc n (beattySeq (β - 1) n) := by
    ext x
    constructor
    · rintro ⟨⟨hlo, hhi⟩, k, hk, rfl⟩
      exact ⟨k, ⟨hmono.lt_iff_lt.mp hlo, (cut hk).mp hhi⟩, rfl⟩
    · rintro ⟨k, ⟨hlo, hhi⟩, rfl⟩
      have hk := hn.trans hlo
      exact ⟨⟨hmono hlo, (cut hk).mpr hhi⟩, k, hk, rfl⟩
  have hβ : 2 < β := by
    rw [hc.conjugate_eq, lt_div_iff₀ hc.sub_one_pos]
    linarith
  have hbound : n ≤ beattySeq (β - 1) n := by
    apply Int.le_floor.mpr
    exact le_mul_of_one_le_right (by exact_mod_cast hn.le) (by linarith)
  rw [himage, ncard_image_of_injective _ hmono.injective, ncard_Ioc,
    Int.card_Ioc_of_le _ _ hbound, beattySeq, beattySeq, ← Int.floor_sub_intCast]
  congr 1
  ring

end MetaMathlibExt
