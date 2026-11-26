/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Rayleigh
import MathlibExt.NumberTheory.Beatty.CountIncrement

/-! # The β-Beatty counts between complementary endpoints form a Beatty sequence

The main result `beatty_card_compl_between_isBeatty` says that for complementary Beatty
sequences with `1 < α < 2`, the counts of `β`-terms strictly between `⌊nα⌋` and `⌊nβ⌋`
are the values `⌊nr⌋` of a Beatty sequence of slope `0 < r < 1`.

Statements from G. Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104 (arXiv:2305.15361).
-/

namespace MetaMathlibExt

open Set

namespace beatty_card_compl_between_isBeatty

/-- For `1 < α < 2`, consecutive `α`-Beatty terms differ by `1` or `2`. -/
private theorem alpha_step {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (m : ℤ) :
    beattySeq α (m + 1) - beattySeq α m = 1 ∨
      beattySeq α (m + 1) - beattySeq α m = 2 := by
  have key : ⌊((m + 1 : ℤ) : ℝ) * α⌋ - ⌊(m : ℝ) * α⌋ = 1 ∨
      ⌊((m + 1 : ℤ) : ℝ) * α⌋ - ⌊(m : ℝ) * α⌋ = 2 := by
    have hmul : ((m + 1 : ℤ) : ℝ) * α = (m : ℝ) * α + α := by push_cast; ring
    have hlo : ⌊(m : ℝ) * α⌋ + 1 ≤ ⌊((m + 1 : ℤ) : ℝ) * α⌋ := by
      rw [hmul, ← Int.floor_add_one]
      exact Int.floor_mono (by linarith)
    have hhi : ⌊((m + 1 : ℤ) : ℝ) * α⌋ ≤ ⌊(m : ℝ) * α⌋ + 2 := by
      rw [hmul]
      have h2 : (m : ℝ) * α + α ≤ (m : ℝ) * α + 1 + 1 := by linarith
      have hmono := Int.floor_mono h2
      rw [Int.floor_add_one, Int.floor_add_one] at hmono
      omega
    omega
  simpa only [beattySeq] using key

/-- For irrational `α` and positive `m`, `⌊m(2 - α)⌋ = 2m - 1 - ⌊mα⌋`. -/
private theorem floor_two_sub_eq {α : ℝ} (hirr : Irrational α) {m : ℤ} (hm : 0 < m) :
    beattySeq (2 - α) m = 2 * m - 1 - beattySeq α m := by
  have key : ⌊(m : ℝ) * (2 - α)⌋ = 2 * m - 1 - ⌊(m : ℝ) * α⌋ := by
    have hx : Irrational ((m : ℝ) * α) := hirr.intCast_mul hm.ne'
    have hne : (m : ℝ) * α ≠ ((⌊(m : ℝ) * α⌋ : ℤ) : ℝ) := fun h ↦ hx.ne_int _ h
    have hlt : ((⌊(m : ℝ) * α⌋ : ℤ) : ℝ) < (m : ℝ) * α :=
      (Int.floor_le _).lt_of_ne (fun h ↦ hne h.symm)
    have hhi : (m : ℝ) * α < ((⌊(m : ℝ) * α⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hform : (m : ℝ) * (2 - α) = 2 * (m : ℝ) - (m : ℝ) * α := by ring
    rw [hform, Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  simpa only [beattySeq] using key

/-- The `β`-Beatty count at `1` vanishes. -/
private theorem card_one {α β : ℝ} (hα1 : 1 < α) (hαβ : α⁻¹ + β⁻¹ = 1) :
    ((Ioo (beattySeq α 1) (beattySeq β 1) ∩ {beattySeq β k | k > 0}).ncard : ℤ) = 0 := by
  have hc := Real.holderConjugate_iff.mpr ⟨hα1, hαβ⟩
  have hempty :
      Ioo (beattySeq α 1) (beattySeq β 1) ∩ {beattySeq β k | k > 0} = ∅ := by
    ext x
    constructor
    · rintro ⟨⟨_, hhi⟩, k, hk, rfl⟩
      have hk1 : (1:ℤ) ≤ k := by omega
      have hmul : (1:ℝ) * β ≤ (k:ℝ) * β :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hk1) hc.symm.pos.le
      have hle : beattySeq β 1 ≤ beattySeq β k := by
        simpa only [beattySeq, Int.cast_one, one_mul] using Int.floor_mono hmul
      omega
    · intro h
      exact absurd h (Set.notMem_empty x)
  rw [hempty, Set.ncard_empty, Nat.cast_zero]

/-- `⌊2 - α⌋ = 0` for `1 < α < 2`. -/
private theorem floor_two_sub_one {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) :
    beattySeq (2 - α) 1 = 0 := by
  have key : ⌊(2 - α)⌋ = 0 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  simpa only [beattySeq, Int.cast_one, one_mul] using key

/-- The count and `⌊m(2 - α)⌋` grow by the same increment. -/
private theorem card_step {α β : ℝ} (hirr : Irrational α) (hα1 : 1 < α) (hα2 : α < 2)
    (hαβ : α⁻¹ + β⁻¹ = 1) {m : ℤ} (hm : 0 < m) :
    ((Ioo (beattySeq α (m + 1)) (beattySeq β (m + 1)) ∩
      {beattySeq β k | k > 0}).ncard : ℤ) -
        ((Ioo (beattySeq α m) (beattySeq β m) ∩ {beattySeq β k | k > 0}).ncard : ℤ) =
      beattySeq (2 - α) (m + 1) - beattySeq (2 - α) m := by
  have hpub : (((Ioo (beattySeq α (m + 1)) (beattySeq β (m + 1)) ∩
      {beattySeq β k | k > 0}).ncard : ℤ) -
        ((Ioo (beattySeq α m) (beattySeq β m) ∩ {beattySeq β k | k > 0}).ncard : ℤ) = 0 ∨
      ((Ioo (beattySeq α (m + 1)) (beattySeq β (m + 1)) ∩
        {beattySeq β k | k > 0}).ncard : ℤ) -
        ((Ioo (beattySeq α m) (beattySeq β m) ∩ {beattySeq β k | k > 0}).ncard : ℤ) = 1) ∧
      (((Ioo (beattySeq α (m + 1)) (beattySeq β (m + 1)) ∩
        {beattySeq β k | k > 0}).ncard : ℤ) -
          ((Ioo (beattySeq α m) (beattySeq β m) ∩ {beattySeq β k | k > 0}).ncard : ℤ) = 1 ↔
        beattySeq α (m + 1) - beattySeq α m = 1) :=
    beatty_card_compl_between_succ_sub hirr hα1 hα2 hαβ hm
  obtain ⟨h01, hiff⟩ := hpub
  have hα := alpha_step hα1 hα2 m
  have hg : beattySeq (2 - α) (m + 1) - beattySeq (2 - α) m =
      2 - (beattySeq α (m + 1) - beattySeq α m) := by
    rw [floor_two_sub_eq hirr (by omega : 0 < m + 1), floor_two_sub_eq hirr hm]
    ring
  omega

/-- The `β`-Beatty counts between the endpoints equal `⌊n(2 - α)⌋`. -/
private theorem card_eq_floor {α β : ℝ} (hirr : Irrational α) (hα1 : 1 < α) (hα2 : α < 2)
    (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    ((Ioo (beattySeq α n) (beattySeq β n) ∩ {beattySeq β k | k > 0}).ncard : ℤ) =
      beattySeq (2 - α) n := by
  have key : ∀ t : ℕ, 1 ≤ t →
      ((Ioo (beattySeq α t) (beattySeq β t) ∩ {beattySeq β k | k > 0}).ncard : ℤ) =
        beattySeq (2 - α) t := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      rw [Nat.cast_one, card_one hα1 hαβ, floor_two_sub_one hα1 hα2]
    | succ t ht ih =>
      have ht0 : 0 < t := by omega
      have hm : (0:ℤ) < (t:ℤ) := by exact_mod_cast ht0
      have hstep := card_step hirr hα1 hα2 hαβ hm
      push_cast at ⊢
      omega
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, (Int.toNat_of_nonneg hn.le).symm⟩
  have hk0 : 0 < k := by exact_mod_cast hn
  exact key k (by omega)

end beatty_card_compl_between_isBeatty

/-- **The $\beta$-Beatty counts between $\lfloor n\alpha\rfloor$ and $\lfloor n\beta\rfloor$ form a
Beatty sequence.** Let $\alpha$ be an irrational number with $1 < \alpha < 2$, let $\beta$ be a
real number with $\alpha^{-1} + \beta^{-1} = 1$, and let $B$ be the set of the numbers
$\lfloor k\beta\rfloor$ for positive integers $k$. Then there is a real number $r$ with
$0 < r < 1$ such that for every positive integer $n$, the number of elements of $B$ in the open
interval $(\lfloor n\alpha\rfloor, \lfloor n\beta\rfloor)$ equals $\lfloor nr\rfloor$.

By Beatty's theorem, the Beatty sequences of $\alpha$ and $\beta$ are then complementary.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Corollary 3 (`integers-2025-A104-cor-3`). -/
public theorem beatty_card_compl_between_isBeatty {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ n : ℤ, 0 < n →
      ((Ioo (beattySeq α n) (beattySeq β n) ∩ {beattySeq β k | k > 0}).ncard : ℤ) =
        beattySeq r n := by
  refine ⟨2 - α, by linarith, by linarith, fun n hn ↦
    beatty_card_compl_between_isBeatty.card_eq_floor hirr hα1 hα2 hαβ hn⟩

end MetaMathlibExt
