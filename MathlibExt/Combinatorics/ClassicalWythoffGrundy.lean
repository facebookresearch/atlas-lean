/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.Combinatorics.WythoffPass
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.NumberTheory.Rayleigh
import Mathlib.Tactic.Ring

/-!
# Wythoff's theorem for classical Wythoff's game

Rayleigh's theorem partitions the positive naturals between the two Beatty sequences
for `φ` and `φ²`. Together with `(0, 0)`, their paired values give the positions that
have no move to one another and that every other position can move to. The mex recursion
then identifies these positions with Grundy value zero.

The specialization of Rayleigh's theorem parallels the one in
`MathlibExt/Combinatorics/BlockingWythoff.lean`.
-/

namespace MetaMathlibExt

open scoped goldenRatio

namespace ClassicalWythoffGrundy

private noncomputable def lower (n : ℕ) : ℕ := ⌊(n : ℝ) * φ⌋₊

private noncomputable def upper (n : ℕ) : ℕ := lower n + n

private theorem lower_zero : lower 0 = 0 := by simp [lower]

private theorem lower_strictMono : StrictMono lower := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hn : 0 ≤ (n : ℝ) * φ := mul_nonneg n.cast_nonneg Real.goldenRatio_pos.le
  have h : (n : ℝ) * φ + 1 ≤ ((n + 1 : ℕ) : ℝ) * φ := by
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact add_le_add_right Real.one_lt_goldenRatio.le _
  have hf := Nat.floor_le_floor h
  rw [Nat.floor_add_one hn] at hf
  exact hf

private theorem upper_strictMono : StrictMono upper := by
  intro i j hij
  exact add_lt_add (lower_strictMono hij) hij

private theorem upper_eq_floor (n : ℕ) : upper n = ⌊(n : ℝ) * φ ^ 2⌋₊ := by
  unfold upper lower
  rw [Real.goldenRatio_sq, mul_add, mul_one,
    Nat.floor_add_natCast (mul_nonneg n.cast_nonneg Real.goldenRatio_pos.le)]

private theorem mem_beattySeq_pos_iff (r : ℝ) (hr : 0 ≤ r) (k : ℕ) :
    (k : ℤ) ∈ {beattySeq r i | i > 0} ↔ ∃ n : ℕ, 0 < n ∧ ⌊(n : ℝ) * r⌋₊ = k := by
  have cast_floor (n : ℕ) : beattySeq r (n : ℤ) = (⌊(n : ℝ) * r⌋₊ : ℤ) := by
    rw [beattySeq, Int.cast_natCast, Int.natCast_floor_eq_floor (mul_nonneg n.cast_nonneg hr)]
  constructor
  · rintro ⟨i, hi, he⟩
    lift i to ℕ using hi.le
    rw [cast_floor, Nat.cast_inj] at he
    exact ⟨i, by exact_mod_cast hi, he⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, by exact_mod_cast hn, cast_floor n⟩

-- The positive naturals occur in exactly one of the two sequences.
private theorem beatty_partition (k : ℕ) (hk : 0 < k) :
    ((∃ n, 0 < n ∧ lower n = k) ∧ ¬(∃ n, 0 < n ∧ upper n = k)) ∨
      ((∃ n, 0 < n ∧ upper n = k) ∧ ¬(∃ n, 0 < n ∧ lower n = k)) := by
  have hc : Real.HolderConjugate φ (φ ^ 2) := by
    refine Real.holderConjugate_iff.mpr ⟨Real.one_lt_goldenRatio, ?_⟩
    rw [← inv_pow, Real.inv_goldenRatio, neg_sq, Real.goldenConj_sq]
    ring
  have h := Real.goldenRatio_irrational.beattySeq_symmDiff_beattySeq_pos hc
  have hk' : (k : ℤ) ∈ {j : ℤ | 0 < j} := by
    change (0 : ℤ) < k
    exact_mod_cast hk
  simpa only [Set.mem_symmDiff, mem_beattySeq_pos_iff _ Real.goldenRatio_pos.le,
    mem_beattySeq_pos_iff _ (sq_nonneg φ), lower, upper_eq_floor] using h.ge hk'

private theorem endpoints_coincide {i j : ℕ} (h : lower i = upper j) : i = 0 ∧ j = 0 := by
  by_cases hi : i = 0
  · rw [hi, lower_zero, upper] at h
    exact ⟨hi, by omega⟩
  by_cases hj : j = 0
  · have hpos := lower_strictMono (Nat.pos_of_ne_zero hi)
    simp only [hj, upper, lower_zero, Nat.zero_add] at h
    rw [lower_zero] at hpos
    omega
  have hpos : 0 < lower i := lower_zero ▸ lower_strictMono (Nat.pos_of_ne_zero hi)
  rcases beatty_partition (lower i) hpos with ⟨_, hUpper⟩ | ⟨_, hLower⟩
  · exact (hUpper ⟨j, Nat.pos_of_ne_zero hj, h.symm⟩).elim
  · exact (hLower ⟨i, Nat.pos_of_ne_zero hi, rfl⟩).elim

private def Paired (x y : ℕ) : Prop :=
  ∃ n, (x = lower n ∧ y = upper n) ∨ (x = upper n ∧ y = lower n)

private theorem paired_swap {x y : ℕ} : Paired x y → Paired y x := by
  rintro ⟨n, h | h⟩
  · exact ⟨n, Or.inr h.symm⟩
  · exact ⟨n, Or.inl h.symm⟩

-- A coordinate determines its partner, even at the origin where the sequences meet.
private theorem paired_unique {x y z : ℕ} (hy : Paired x y) (hz : Paired x z) : y = z := by
  obtain ⟨i, hi⟩ := hy
  obtain ⟨j, hj⟩ := hz
  rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hj with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · rw [lower_strictMono.injective h]
  · obtain ⟨rfl, rfl⟩ := endpoints_coincide h
    simp [upper]
  · obtain ⟨rfl, rfl⟩ := endpoints_coincide h.symm
    simp [upper]
  · rw [upper_strictMono.injective h]

-- The signed difference is `n` or `-n`; it determines the first coordinate of the pair.
private theorem paired_diagonal_unique {x y u v : ℕ} (hxy : Paired x y) (huv : Paired u v)
    (hdiff : x + v = u + y) : x = u := by
  obtain ⟨i, hi⟩ := hxy
  obtain ⟨j, hj⟩ := huv
  dsimp only [upper] at hi hj
  rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    have hij : i = j := by omega
  all_goals subst j; omega

-- The three kinds of classical Wythoff move, with the same bounds as the mex recursion.
private def Avoids (P : ℕ → ℕ → Prop) (x y : ℕ) : Prop :=
  (∀ u < x, ¬P u y) ∧ (∀ v < y, ¬P x v) ∧
    (∀ t, 1 ≤ t → t ≤ x → t ≤ y → ¬P (x - t) (y - t))

private theorem avoids_swap {x y : ℕ} (h : Avoids Paired x y) : Avoids Paired y x :=
  ⟨fun u hu hp => h.2.1 u hu (paired_swap hp), fun v hv hp => h.1 v hv (paired_swap hp),
    fun t ht hx hy hp => h.2.2 t ht hy hx (paired_swap hp)⟩

private theorem paired_stable {x y : ℕ} (h : Paired x y) : Avoids Paired x y := by
  refine ⟨fun u hu hp => ?_, fun v hv hp => ?_, fun t ht htx hty hp => ?_⟩
  · exact (ne_of_gt hu) (paired_unique (paired_swap h) (paired_swap hp))
  · exact (ne_of_gt hv) (paired_unique h hp)
  · have := paired_diagonal_unique h hp (by omega)
    omega

private theorem paired_of_avoids_of_le {x y : ℕ} (hxy : x ≤ y) (h : Avoids Paired x y) :
    Paired x y := by
  let d := y - x
  have hy : y = x + d := by dsimp [d]; omega
  rcases lt_trichotomy (lower d) x with hdiag | heq | hsmall
  · -- A diagonal move reaches the pair with difference `d`.
    exfalso
    apply h.2.2 (x - lower d) (by omega) (by omega) (by omega)
    exact ⟨d, Or.inl ⟨by omega, by unfold upper; omega⟩⟩
  · exact ⟨d, Or.inl ⟨heq.symm, by unfold upper; omega⟩⟩
  · -- A vertical move reaches the pair containing `x`.
    exfalso
    by_cases hx : x = 0
    · have hypos : 0 < y := by
        by_contra! hzero
        have hd : d = 0 := by dsimp [d]; omega
        rw [hd, lower_zero] at hsmall
        omega
      exact h.2.1 0 hypos ⟨0, Or.inl ⟨hx.trans lower_zero.symm, by simp [upper, lower_zero]⟩⟩
    rcases beatty_partition x (Nat.pos_of_ne_zero hx) with ⟨⟨i, _, hi⟩, _⟩ | ⟨⟨i, hi, he⟩, _⟩
    · have hid : i < d := lower_strictMono.lt_iff_lt.mp (hi ▸ hsmall)
      exact h.2.1 (upper i) (by unfold upper; omega) ⟨i, Or.inl ⟨hi.symm, rfl⟩⟩
    · exact h.2.1 (lower i) (by unfold upper at he; omega) ⟨i, Or.inr ⟨he.symm, rfl⟩⟩

private theorem avoids_paired_iff (x y : ℕ) : Avoids Paired x y ↔ Paired x y := by
  refine ⟨fun h => ?_, paired_stable⟩
  rcases le_total x y with hxy | hyx
  · exact paired_of_avoids_of_le hxy h
  · exact paired_swap (paired_of_avoids_of_le hyx (avoids_swap h))

local notation "grundy" => fun x y => wythoffPassGrundy x y false

private theorem grundy_zero_iff_avoids (x y : ℕ) :
    grundy x y = 0 ↔ Avoids (fun u v => grundy u v = 0) x y := by
  let missing : Set ℕ := {m | Avoids (fun u v => grundy u v = m) x y}
  have heq : grundy x y = sInf missing := by
    change wythoffExtraMoveGrundy true x y false = _
    rw [wythoffExtraMoveGrundy_eq]
    simp [missing, Avoids]
  -- One more than the maximum of the three finite option families is not attained.
  let a := (Finset.range x).sup (fun u => grundy u y)
  let b := (Finset.range y).sup (fun v => grundy x v)
  let c := (Finset.range (min x y + 1)).sup (fun t => grundy (x - t) (y - t))
  let m := max (max a b) c + 1
  have hmissing : missing.Nonempty := by
    refine ⟨m, ?_⟩
    change Avoids (fun u v => grundy u v = m) x y
    refine ⟨fun u hu => ?_, fun v hv => ?_, fun t _ htx hty => ?_⟩
    · have ha : grundy u y ≤ a := Finset.le_sup (f := fun i => grundy i y) (Finset.mem_range.mpr hu)
      exact ne_of_lt (Nat.lt_succ_of_le ((ha.trans (le_max_left a b)).trans (le_max_left _ c)))
    · have hb : grundy x v ≤ b := Finset.le_sup (f := fun i => grundy x i) (Finset.mem_range.mpr hv)
      exact ne_of_lt (Nat.lt_succ_of_le ((hb.trans (le_max_right a b)).trans (le_max_left _ c)))
    · have ht : t < min x y + 1 := Nat.lt_succ_of_le (le_min htx hty)
      have hc : grundy (x - t) (y - t) ≤ c :=
        Finset.le_sup (f := fun i => grundy (x - i) (y - i)) (Finset.mem_range.mpr ht)
      exact ne_of_lt (Nat.lt_succ_of_le (hc.trans (le_max_right _ c)))
  change grundy x y = 0 ↔ 0 ∈ missing
  rw [heq]
  exact ⟨fun h => h ▸ Nat.sInf_mem hmissing, fun h => Nat.eq_zero_of_le_zero (Nat.sInf_le h)⟩

private theorem grundy_zero_iff_paired (x y : ℕ) : grundy x y = 0 ↔ Paired x y := by
  rw [grundy_zero_iff_avoids, ← avoids_paired_iff]
  unfold Avoids
  refine and_congr (forall_congr' fun u => forall_congr' fun hu => ?_)
    (and_congr (forall_congr' fun v => forall_congr' fun hv => ?_)
      (forall_congr' fun t => forall_congr' fun ht => forall_congr' fun htx =>
        forall_congr' fun hty => ?_))
  · exact (grundy_zero_iff_paired u y).not
  · exact (grundy_zero_iff_paired x v).not
  · exact (grundy_zero_iff_paired (x - t) (y - t)).not
termination_by x + y
decreasing_by all_goals omega

end ClassicalWythoffGrundy

/-- **Wythoff's theorem.** Let $\mathcal{G}_1(x, y, 0)$ be the Grundy number of the position
$(x, y, 0)$ of Wythoff's game with a pass, in which the pass has been used; this is the Grundy
number of $(x, y)$ in classical Wythoff's game. Then $\mathcal{G}_1(x, y, 0) = 0$ (that is,
$(x, y)$ is a P-position) if and only if there is $n \in \mathbb{N}$ with
$(x, y) = (\lfloor n\varphi \rfloor, \lfloor n\varphi \rfloor + n)$ or
$(x, y) = (\lfloor n\varphi \rfloor + n, \lfloor n\varphi \rfloor)$, where
$\varphi = (1 + \sqrt{5})/2$ is the golden ratio.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Theorem 2 (`integers-2025-G4-thm-2`), quoting Wythoff. -/
public theorem wythoffGrundy_eq_zero_iff (x y : ℕ) :
    wythoffPassGrundy x y false = 0 ↔
      ∃ n : ℕ, (x = ⌊(n : ℝ) * Real.goldenRatio⌋₊ ∧ y = ⌊(n : ℝ) * Real.goldenRatio⌋₊ + n) ∨
        (x = ⌊(n : ℝ) * Real.goldenRatio⌋₊ + n ∧ y = ⌊(n : ℝ) * Real.goldenRatio⌋₊) :=
  ClassicalWythoffGrundy.grundy_zero_iff_paired x y

end MetaMathlibExt
