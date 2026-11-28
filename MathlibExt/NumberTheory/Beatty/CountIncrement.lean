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

/-! # Increments of the counts between complementary Beatty sequences -/

namespace MetaMathlibExt

open Set

namespace beatty_card_compl_between_succ_sub

private theorem strictMono_beattySeq {s : ℝ} (hs : 1 ≤ s) : StrictMono (beattySeq s) := by
  apply strictMono_int_of_lt_succ
  intro j
  simp only [beattySeq, Int.cast_add, Int.cast_one, add_mul, one_mul]
  rw [← Int.add_one_le_iff, ← Int.floor_add_one]
  exact Int.floor_mono (add_le_add_right hs _)

/-- The contributing β-indices are exactly the integers strictly between `⌊mα⌋ - m` and `m`. -/
private theorem count {α β : ℝ} (hirr : Irrational α) (hc : α.HolderConjugate β)
    (hα2 : α < 2) {m : ℤ} (hm : 0 < m) :
    ((Ioo (beattySeq α m) (beattySeq β m) ∩ {beattySeq β k | k > 0}).ncard : ℤ) =
      m - (beattySeq α m - m) - 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have ha : m ≤ beattySeq α m :=
    Int.le_floor.mpr (le_mul_of_one_le_right hm'.le hc.lt.le)
  have ha' : beattySeq α m < 2 * m := by
    apply Int.floor_lt.mpr
    push_cast
    simpa only [mul_comm (2 : ℝ)] using mul_lt_mul_of_pos_left hα2 hm'
  have hb := strictMono_beattySeq hc.symm.lt.le
  have cut {k : ℤ} (hk : 0 < k) :
      beattySeq α m < beattySeq β k ↔ beattySeq α m - m < k := by
    -- Rayleigh's theorem rules out a tie between the two floors.
    have hpos : beattySeq α m ∈ {j : ℤ | 0 < j} := hm.trans_le ha
    rw [← hirr.beattySeq_symmDiff_beattySeq_pos hc, mem_symmDiff] at hpos
    have hne : beattySeq α m ≠ beattySeq β k := fun h ↦
      hpos.elim (fun hp ↦ hp.2 ⟨k, hk, h.symm⟩) (fun hp ↦ hp.2 ⟨m, hm, rfl⟩)
    calc
      beattySeq α m < beattySeq β k ↔ (m : ℝ) * α < k * β :=
        ⟨Int.floor_mono.reflect_lt, fun h ↦ (Int.floor_mono h.le).lt_of_ne hne⟩
      _ ↔ beattySeq α m - m < k := by
        rw [← div_lt_iff₀ hc.symm.pos, mul_div_assoc, hc.div_conj_eq_sub_one, mul_sub, mul_one,
          ← Int.floor_lt, Int.floor_sub_intCast]
        rfl
  have himage : Ioo (beattySeq α m) (beattySeq β m) ∩ {beattySeq β k | k > 0} =
      beattySeq β '' Ioo (beattySeq α m - m) m := by
    ext x
    constructor
    · rintro ⟨⟨hlo, hhi⟩, k, hk, rfl⟩
      exact ⟨k, ⟨(cut hk).mp hlo, hb.lt_iff_lt.mp hhi⟩, rfl⟩
    · rintro ⟨k, ⟨hlo, hhi⟩, rfl⟩
      have hk : 0 < k := by omega
      exact ⟨⟨(cut hk).mpr hlo, hb hhi⟩, k, hk, rfl⟩
  rw [himage, ncard_image_of_injective _ hb.injective, ncard_Ioo, Int.card_Ioo_of_lt]
  omega

end beatty_card_compl_between_succ_sub

/-- **Increments of the $\beta$-Beatty counts between $\lfloor n\alpha\rfloor$ and
$\lfloor n\beta\rfloor$.** Let $\alpha$ be an irrational number with $1 < \alpha < 2$, let $\beta$
be a real number with $\alpha^{-1} + \beta^{-1} = 1$, let $B$ be the set of the numbers
$\lfloor k\beta\rfloor$ for positive integers $k$, and for an integer $m$ let $r(m)$ be the number
of elements of $B$ in the open interval $(\lfloor m\alpha\rfloor, \lfloor m\beta\rfloor)$. Then for
every positive integer $n$, the difference $r(n + 1) - r(n)$ is $0$ or $1$, and it equals $1$ if
and only if $\lfloor (n + 1)\alpha\rfloor - \lfloor n\alpha\rfloor = 1$.

By Beatty's theorem, the Beatty sequences of $\alpha$ and $\beta$ are then complementary.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Lemma 4 (`integers-2025-A104-lem-4`). -/
public theorem beatty_card_compl_between_succ_sub {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    let r : ℤ → ℤ := fun m ↦
      ((Ioo (beattySeq α m) (beattySeq β m) ∩ {beattySeq β k | k > 0}).ncard : ℤ)
    (r (n + 1) - r n = 0 ∨ r (n + 1) - r n = 1) ∧
      (r (n + 1) - r n = 1 ↔ beattySeq α (n + 1) - beattySeq α n = 1) := by
  have hc := Real.holderConjugate_iff.mpr ⟨hα1, hαβ⟩
  dsimp only
  rw [beatty_card_compl_between_succ_sub.count hirr hc hα2 (by omega : 0 < n + 1),
    beatty_card_compl_between_succ_sub.count hirr hc hα2 hn]
  have hlo := beatty_card_compl_between_succ_sub.strictMono_beattySeq hα1.le (lt_add_one n)
  have hhi : beattySeq α (n + 1) ≤ beattySeq α n + 2 := by
    simp only [beattySeq, Int.cast_add, Int.cast_one, add_mul, one_mul, ← Int.floor_add_ofNat]
    exact Int.floor_mono (add_le_add_right hα2.le _)
  omega

end MetaMathlibExt
