/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Ordinary moment recurrence for Irwin series

The solutions have nonnegative moments, decrease with the degree, and increase with the digit
count to the moments of the uniform measure of mass equal to the base.
-/

namespace MetaMathlibExt

open Filter Finset

@[expose] public section

/-- **Digit power sum.** For natural numbers $b$, $d$ and $j$, the digit power sum $\gamma_j$ is
the real number $\sum_{0 \le a < b,\ a \ne d} a^j$, the sum of the $j$-th powers of the base-$b$
digits other than $d$, with the convention $0^0 = 1$.

Source: Jean-François Burnol, *Measures for the Summation of Irwin Series*,
INTEGERS 26 (2026), Article A11, Theorem 1. -/
public def digitPowerSum (b d j : ℕ) : ℝ :=
  ∑ a ∈ Finset.range b, if a = d then 0 else (a : ℝ) ^ j

/-- **Ordinary moment recurrence.** Let $b$ and $d$ be natural numbers, and for $i \ge 1$ let
$\gamma_i$ be the sum of the $i$-th powers of the base-$b$ digits $a \in \{0, \dots, b-1\}$ with
$a \ne d$. A family of real numbers $(u_{j;m})_{j, m \in \mathbb{N}}$ satisfies the ordinary
moment recurrence for $b$ and $d$ when $u_{0;0} = b$, when for every $m \ge 1$

$$
(b^{m+1} - b + 1)\, u_{0;m} = \sum_{i=1}^{m} \binom{m}{i} \gamma_i\, u_{0;m-i},
$$

and when for every $j \ge 1$ and every $m \ge 0$

$$
(b^{m+1} - b + 1)\, u_{j;m} = \sum_{i=1}^{m} \binom{m}{i} \gamma_i\, u_{j;m-i} +
\sum_{i=0}^{m} \binom{m}{i} d^i\, u_{j-1;m-i}.
$$

Source: Jean-François Burnol, *Measures for the Summation
of Irwin Series*, INTEGERS 26 (2026), Article A11, Theorem 1. -/
public def OrdinaryMomentRecurrence (b d : ℕ) (u : ℕ → ℕ → ℝ) : Prop :=
  u 0 0 = b ∧
    (∀ m, 1 ≤ m →
      (((b : ℝ) ^ (m + 1) - b + 1) * u 0 m =
        ∑ i ∈ Finset.Icc 1 m,
          (Nat.choose m i : ℝ) * digitPowerSum b d i * u 0 (m - i))) ∧
    (∀ j, 1 ≤ j → ∀ m,
      (((b : ℝ) ^ (m + 1) - b + 1) * u j m =
        (∑ i ∈ Finset.Icc 1 m,
          (Nat.choose m i : ℝ) * digitPowerSum b d i * u j (m - i)) +
        ∑ i ∈ Finset.range (m + 1),
          (Nat.choose m i : ℝ) * (d : ℝ) ^ i * u (j - 1) (m - i)))

end

namespace ordinaryMomentRecurrence_properties

-- The binomial expansion of the translated moment of degree m.
private def translate (a : ℕ) (v : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ range (m + 1), (m.choose i : ℝ) * (a : ℝ) ^ i * v (m - i)

private def lower (a : ℕ) (v : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Icc 1 m, (m.choose i : ℝ) * (a : ℝ) ^ i * v (m - i)

private theorem translate_split (a : ℕ) (v : ℕ → ℝ) (m : ℕ) :
    translate a v m = v m + lower a v m := by
  have hr : range (m + 1) = insert 0 (Icc 1 m) := by ext i; simp; omega
  simp [translate, lower, hr]

private theorem translate_sub (a : ℕ) (v w : ℕ → ℝ) (m : ℕ) :
    translate a (fun k => v k - w k) m = translate a v m - translate a w m := by
  simp [translate, mul_sub, sum_sub_distrib]

private theorem translate_succ (a : ℕ) (v : ℕ → ℝ) (m : ℕ) :
    translate a v (m + 1) =
      translate a (fun k => v (k + 1)) m + a * translate a v m := by
  unfold translate
  simp only [mul_assoc]
  rw [sum_choose_succ_mul (fun i k => (a : ℝ) ^ i * v k), mul_sum]
  congr 1
  · refine sum_congr rfl fun i hi => ?_
    rw [show m + 1 - i = (m - i) + 1 by have := mem_range.mp hi; omega]
  · refine sum_congr rfl fun i _ => ?_
    rw [pow_succ]
    ring

private theorem translate_nonneg {v : ℕ → ℝ} (hv : ∀ k, 0 ≤ v k) (a m : ℕ) :
    0 ≤ translate a v m :=
  sum_nonneg fun i _ => mul_nonneg (by positivity) (hv _)

private theorem translate_pos {v : ℕ → ℝ} (hv : ∀ k, 0 ≤ v k)
    {a m : ℕ} (ha : 0 < a) (h0 : 0 < v 0) : 0 < translate a v m := by
  apply sum_pos' (fun i _ => mul_nonneg (by positivity) (hv _))
  exact ⟨m, by simp, by simpa using mul_pos (pow_pos (Nat.cast_pos.mpr ha) m) h0⟩

-- Isolate the contribution of the unshifted moment (i = 0) to the digit sum.
private def residual (s : Finset ℕ) (c : ℝ) (v : ℕ → ℝ) (m : ℕ) : ℝ :=
  c * v m - ∑ a ∈ s, translate a v m

private theorem residual_eq (s : Finset ℕ) (c : ℝ) (v : ℕ → ℝ) (m : ℕ) :
    residual s c v m = (c - s.card) * v m - ∑ a ∈ s, lower a v m := by
  simp [residual, translate_split, sum_add_distrib, nsmul_eq_mul]
  ring

private theorem residual_sub (s : Finset ℕ) (c : ℝ) (v w : ℕ → ℝ) (m : ℕ) :
    residual s c (fun k => v k - w k) m = residual s c v m - residual s c w m := by
  simp [residual, translate_sub, sum_sub_distrib]
  ring

private theorem lower_nonneg {m : ℕ} {v : ℕ → ℝ} (hv : ∀ k < m, 0 ≤ v k) (a : ℕ) :
    0 ≤ lower a v m := by
  refine sum_nonneg fun i hi => mul_nonneg (by positivity) (hv _ ?_)
  have := mem_Icc.mp hi
  omega

private theorem nonneg_of_residual {s : Finset ℕ} {c : ℕ → ℝ} {v : ℕ → ℝ}
    (hc : ∀ m, (s.card : ℝ) < c m) (h : ∀ m, 0 ≤ residual s (c m) v m) :
    ∀ m, 0 ≤ v m := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    have he := h m
    rw [residual_eq] at he
    have hs := sum_nonneg (s := s) fun a _ => lower_nonneg ih a
    exact nonneg_of_mul_nonneg_right (by linarith) (sub_pos.mpr (hc m))

private theorem pos_of_residual {s : Finset ℕ} {c : ℝ} {v : ℕ → ℝ} {m : ℕ}
    (hc : (s.card : ℝ) < c) (hv : ∀ k, 0 ≤ v k) (h : 0 < residual s c v m) :
    0 < v m := by
  rw [residual_eq] at h
  have hs := sum_nonneg (s := s) fun a _ => lower_nonneg (m := m) (fun k _ => hv k) a
  exact pos_of_mul_pos_right (by linarith) (sub_nonneg.mpr hc.le)

private theorem pos_of_digit {s : Finset ℕ} {c : ℝ} {v : ℕ → ℝ} {m a : ℕ}
    (hc : (s.card : ℝ) < c) (hv : ∀ k, 0 ≤ v k) (h : 0 ≤ residual s c v m)
    (ha : a ∈ s) (ha' : 0 < a) (hm : 1 ≤ m) (h0 : 0 < v 0) : 0 < v m := by
  rw [residual_eq] at h
  have hs : 0 < ∑ n ∈ s, lower n v m := by
    apply sum_pos' (fun n _ => lower_nonneg (fun k _ => hv k) n)
    refine ⟨a, ha, sum_pos' (fun i _ => mul_nonneg (by positivity) (hv _)) ?_⟩
    exact ⟨m, mem_Icc.mpr ⟨hm, le_rfl⟩,
      by simpa using mul_pos (pow_pos (Nat.cast_pos.mpr ha') m) h0⟩
  exact pos_of_mul_pos_right (by linarith) (sub_nonneg.mpr hc.le)

private abbrev digits (b d : ℕ) := (range b).erase d

private theorem card_digits {b d : ℕ} (hd : d < b) : ((digits b d).card : ℝ) = b - 1 := by
  rw [card_erase_of_mem (mem_range.mpr hd), card_range, Nat.cast_sub (by omega)]
  simp

private theorem coeff_lt {b d : ℕ} (hb : 1 < b) (hd : d < b) (m : ℕ) :
    ((digits b d).card : ℝ) < (b : ℝ) ^ (m + 1) := by
  rw [card_digits hd]
  have hb' : 1 ≤ (b : ℝ) := by exact_mod_cast hb.le
  have hp := pow_le_pow_right₀ hb' (show 1 ≤ m + 1 by omega)
  simp only [pow_one] at hp
  linarith

private theorem sum_lower (b d : ℕ) (v : ℕ → ℝ) (m : ℕ) :
    ∑ a ∈ digits b d, lower a v m =
      ∑ i ∈ Icc 1 m, (m.choose i : ℝ) * digitPowerSum b d i * v (m - i) := by
  unfold lower digitPowerSum
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  have h (a : ℕ) : (if a = d then 0 else (a : ℝ) ^ i) =
      (if a ≠ d then (a : ℝ) ^ i else 0) := by split_ifs <;> simp_all
  simp_rw [h]
  rw [← sum_filter, filter_ne']
  simp [mul_sum, sum_mul]

private def forcing (b d : ℕ) (u : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, m => if m = 0 then b else 0
  | j + 1, m => translate d (u j) m

variable {b d : ℕ} {u : ℕ → ℕ → ℝ}

private theorem row_eq (hd : d < b) (hu : OrdinaryMomentRecurrence b d u) (j m : ℕ) :
    residual (digits b d) ((b : ℝ) ^ (m + 1)) (u j) m = forcing b d u j m := by
  rw [residual_eq, card_digits hd, sum_lower, show (b : ℝ) ^ (m + 1) - (b - 1) =
    (b : ℝ) ^ (m + 1) - b + 1 by ring]
  cases j with
  | zero =>
    cases m with
    | zero => simp [forcing, hu.1]
    | succ m =>
      have h := hu.2.1 (m + 1) (by omega)
      simp only [forcing, Nat.succ_ne_zero, ↓reduceIte]
      linarith
  | succ j =>
    have h := hu.2.2 (j + 1) (by omega) m
    simpa only [Nat.add_sub_cancel, forcing, translate] using sub_eq_of_eq_add' h

private theorem degree_zero (hu : OrdinaryMomentRecurrence b d u) (j : ℕ) : u j 0 = b := by
  induction j with
  | zero => exact hu.1
  | succ j ih => simpa [ih] using hu.2.2 (j + 1) (by omega) 0

private theorem moment_nonneg (hb : 1 < b) (hd : d < b) (hu : OrdinaryMomentRecurrence b d u)
    (j : ℕ) : ∀ m, 0 ≤ u j m := by
  induction j with
  | zero =>
    apply nonneg_of_residual (coeff_lt hb hd)
    intro m
    rw [row_eq hd hu]
    simp [forcing, apply_ite]
  | succ j ih =>
    apply nonneg_of_residual (coeff_lt hb hd)
    intro m
    rw [row_eq hd hu]
    exact translate_nonneg ih d m

private theorem exists_pos_digit (hb : 1 < b) (he : ¬(b = 2 ∧ d = 1)) :
    ∃ a ∈ digits b d, 0 < a := by
  by_cases h : d = 1
  · exact ⟨2, mem_erase.mpr ⟨by omega, mem_range.mpr (by omega)⟩, by decide⟩
  · exact ⟨1, mem_erase.mpr ⟨Ne.symm h, mem_range.mpr hb⟩, by decide⟩

private theorem exceptional_zero (hu : OrdinaryMomentRecurrence 2 1 u) {m : ℕ} (hm : 1 ≤ m) :
    u 0 m = 0 := by
  have h := hu.2.1 m hm
  have hz (i : ℕ) (hi : i ∈ Icc 1 m) : digitPowerSum 2 1 i = 0 := by
    have hip : i ≠ 0 := by have := mem_Icc.mp hi; omega
    norm_num [digitPowerSum, sum_range_succ, hip]
  rw [sum_eq_zero (fun i hi => by rw [hz i hi]; ring)] at h
  apply (mul_eq_zero.mp h).resolve_left
  have hc := coeff_lt (b := 2) (d := 1) (by decide) (by decide) m
  rw [card_digits (by decide : 1 < 2)] at hc
  push_cast at *
  linarith

private theorem moment_zero_iff (hb : 1 < b) (hd : d < b) (hu : OrdinaryMomentRecurrence b d u)
    (j m : ℕ) (hm : 1 ≤ m) : u j m = 0 ↔ j = 0 ∧ b = 2 ∧ d = 1 := by
  have h0 (j : ℕ) : 0 < u j 0 := by rw [degree_zero hu]; exact_mod_cast (by omega : 0 < b)
  have hn := moment_nonneg hb hd hu
  constructor
  · contrapose!
    intro h
    apply ne_of_gt
    by_cases he : b = 2 ∧ d = 1
    · obtain ⟨rfl, rfl⟩ := he
      cases j with
      | zero => simp at h
      | succ j =>
        apply pos_of_residual (coeff_lt hb hd m) (hn _)
        rw [row_eq hd hu]
        exact translate_pos (hn j) (by decide : 0 < 1) (h0 j)
    · obtain ⟨a, ha, ha'⟩ := exists_pos_digit hb he
      apply pos_of_digit (coeff_lt hb hd m) (hn j) _ ha ha' hm (h0 j)
      rw [row_eq hd hu]
      cases j with
      | zero => simp [forcing, show m ≠ 0 by omega]
      | succ j => exact translate_nonneg (hn j) _ _
  · rintro ⟨rfl, rfl, rfl⟩
    exact exceptional_zero hu hm

private theorem translate_ge {v : ℕ → ℝ} (hv : ∀ k, 0 ≤ v k) (a m : ℕ) :
    v m ≤ translate a v m := by
  rw [translate_split]
  exact le_add_of_nonneg_right (lower_nonneg (fun k _ => hv k) a)

private theorem increasing (hb : 1 < b) (hd : d < b) (hu : OrdinaryMomentRecurrence b d u)
    (j : ℕ) : ∀ m, 1 ≤ m → u j m < u (j + 1) m := by
  have lift (n : ℕ) (hs : ∀ m, 1 ≤ m → forcing b d u n m < forcing b d u (n + 1) m) :
      ∀ m, 1 ≤ m → u n m < u (n + 1) m := by
    let v := fun k => u (n + 1) k - u n k
    have step (m : ℕ) (hm : 1 ≤ m) :
        0 < residual (digits b d) ((b : ℝ) ^ (m + 1)) v m := by
      dsimp [v]
      rw [residual_sub, row_eq hd hu, row_eq hd hu]
      exact sub_pos.mpr (hs m hm)
    have hn : ∀ m, 0 ≤ v m := nonneg_of_residual (coeff_lt hb hd) (fun m => by
      cases m with
      | zero => simp [v, residual, translate, degree_zero hu]
      | succ m => exact (step _ (by omega)).le)
    exact fun m hm => sub_pos.mp (pos_of_residual (coeff_lt hb hd m) hn (step m hm))
  induction j with
  | zero =>
    apply lift
    intro m hm
    simp only [forcing, show m ≠ 0 by omega, ↓reduceIte]
    by_cases h : 0 < d
    · apply translate_pos (moment_nonneg hb hd hu 0) h
      rw [hu.1]
      exact_mod_cast (by omega : 0 < b)
    · have hne : u 0 m ≠ 0 := fun hz => by
        have := (moment_zero_iff hb hd hu 0 m hm).mp hz
        omega
      exact (lt_of_le_of_ne (moment_nonneg hb hd hu 0 m) hne.symm).trans_le
        (translate_ge (moment_nonneg hb hd hu 0) _ _)
  | succ j ih =>
    apply lift
    intro m hm
    apply sub_pos.mp
    change 0 < translate d (u (j + 1)) m - translate d (u j) m
    rw [← translate_sub]
    refine (sub_pos.mpr (ih m hm)).trans_le (translate_ge (v := fun k =>
      u (j + 1) k - u j k) ?_ d m)
    intro k
    cases k with
    | zero => simp [degree_zero hu]
    | succ k => exact (sub_pos.mpr (ih _ (by omega))).le

private abbrev gap (v : ℕ → ℝ) (m : ℕ) := v m - v (m + 1)

private theorem translate_gap (a : ℕ) (v : ℕ → ℝ) (m : ℕ) :
    translate a (gap v) m = (1 + a) * translate a v m - translate a v (m + 1) := by
  change translate a (fun k => v k - v (k + 1)) m = _
  rw [translate_sub, translate_succ]
  ring

-- Comparing consecutive degrees introduces a nonnegative term for each digit a < b.
private theorem gap_residual_ge (hb : 1 < b) (hd : d < b) (hu : OrdinaryMomentRecurrence b d u)
    (j m : ℕ) :
    b * forcing b d u j m - forcing b d u j (m + 1) ≤
      residual (digits b d) ((b : ℝ) ^ (m + 2)) (gap (u j)) m := by
  rw [← row_eq hd hu, ← row_eq hd hu]
  simp only [residual, translate_gap, sum_sub_distrib, gap, mul_sub, mul_sum]
  have hs : ∑ a ∈ digits b d, (1 + (a : ℝ)) * translate a (u j) m ≤
      ∑ a ∈ digits b d, (b : ℝ) * translate a (u j) m := by
    refine sum_le_sum fun a ha => mul_le_mul_of_nonneg_right ?_
      (translate_nonneg (moment_nonneg hb hd hu j) a m)
    have h := mem_range.mp (mem_erase.mp ha).2
    exact_mod_cast (by omega : 1 + a ≤ b)
  rw [show (b : ℝ) ^ (m + 2) = b * (b : ℝ) ^ (m + 1) by rw [pow_succ']]
  linarith only [hs]

private theorem gap_residual_succ_ge (hb : 1 < b) (hd : d < b)
    (hu : OrdinaryMomentRecurrence b d u) (j m : ℕ) :
    translate d (gap (u j)) m ≤
      residual (digits b d) ((b : ℝ) ^ (m + 2)) (gap (u (j + 1))) m := by
  apply le_trans _ (gap_residual_ge hb hd hu (j + 1) m)
  rw [translate_gap]
  apply sub_le_sub_right
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 1 + d ≤ b))
    (translate_nonneg (moment_nonneg hb hd hu j) d m)

private theorem gap_nonneg (hb : 1 < b) (hd : d < b) (hu : OrdinaryMomentRecurrence b d u)
    (j : ℕ) : (∀ m, 0 ≤ gap (u j) m) ∧ 0 < gap (u j) 0 := by
  induction j with
  | zero =>
    have h (m : ℕ) := gap_residual_ge hb hd hu 0 m
    simp only [forcing, Nat.succ_ne_zero, ↓reduceIte, sub_zero] at h
    have hn : ∀ m, 0 ≤ gap (u 0) m := by
      apply nonneg_of_residual (fun m => coeff_lt hb hd (m + 1))
      intro m
      exact le_trans (mul_nonneg (Nat.cast_nonneg _) (by split <;> positivity)) (h m)
    refine ⟨hn, pos_of_residual (coeff_lt hb hd 1) hn ?_⟩
    have h0 := h 0
    simp only [↓reduceIte] at h0
    exact lt_of_lt_of_le (by positivity) h0
  | succ j ih =>
    have h (m : ℕ) := gap_residual_succ_ge hb hd hu j m
    have hn : ∀ m, 0 ≤ gap (u (j + 1)) m :=
      nonneg_of_residual (fun m => coeff_lt hb hd (m + 1))
        (fun m => (translate_nonneg ih.1 d m).trans (h m))
    exact ⟨hn, pos_of_residual (coeff_lt hb hd 1) hn
      (ih.2.trans_le ((translate_ge ih.1 d 0).trans (h 0)))⟩

private theorem gap_pos (hb : 1 < b) (hd : d < b) (hu : OrdinaryMomentRecurrence b d u)
    (j m : ℕ) (hm : 1 ≤ m) (hne : u j m ≠ 0) : 0 < gap (u j) m := by
  have hg := gap_nonneg hb hd hu
  by_cases he : b = 2 ∧ d = 1
  · obtain ⟨rfl, rfl⟩ := he
    cases j with
    | zero => exact (hne (exceptional_zero hu hm)).elim
    | succ j =>
      exact pos_of_residual (coeff_lt hb hd (m + 1)) (hg _).1
        ((translate_pos (hg j).1 (by decide : 0 < 1) (hg j).2).trans_le
          (gap_residual_succ_ge hb hd hu j m))
  · obtain ⟨a, ha, ha'⟩ := exists_pos_digit hb he
    apply pos_of_digit (coeff_lt hb hd (m + 1)) (hg j).1 _ ha ha' hm (hg j).2
    cases j with
    | zero => simpa [forcing, show m ≠ 0 by omega] using gap_residual_ge hb hd hu 0 m
    | succ j => exact (translate_nonneg (hg j).1 d m).trans (gap_residual_succ_ge hb hd hu j m)

private noncomputable abbrev uniformMoment (b m : ℕ) : ℝ := b / ((m : ℝ) + 1)

-- The uniform moments turn the sum over digits into a telescoping sum.
private theorem translate_uniform (b a m : ℕ) :
    translate a (uniformMoment b) m =
      uniformMoment b m * (((a : ℝ) + 1) ^ (m + 1) - (a : ℝ) ^ (m + 1)) := by
  have hpow : ((a : ℝ) + 1) ^ (m + 1) - (a : ℝ) ^ (m + 1) =
      ∑ i ∈ range (m + 1), (a : ℝ) ^ i * (m + 1).choose i := by
    rw [add_pow, sum_range_succ]
    simp
  rw [hpow, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  have h := Nat.choose_mul_succ_eq m i
  rw [show m + 1 - i = (m - i) + 1 by omega] at h
  have hr : (m.choose i : ℝ) * (m + 1) = ((m + 1).choose i : ℝ) * ((m - i : ℕ) + 1) := by
    exact_mod_cast h
  dsimp [uniformMoment]
  field_simp
  linear_combination (a : ℝ) ^ i * b * hr

private theorem uniform_stationary (b m : ℕ) :
    residual (range b) ((b : ℝ) ^ (m + 1)) (uniformMoment b) m = 0 := by
  simp only [residual, translate_uniform, ← mul_sum]
  have ht := sum_range_sub (fun n : ℕ => (n : ℝ) ^ (m + 1)) b
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_pow (Nat.succ_ne_zero _),
    sub_zero] at ht
  rw [ht]
  ring

private theorem translate_tendsto {v : ℕ → ℕ → ℝ} {l : ℕ → ℝ}
    (hl : ∀ m, Tendsto (fun j => v j m) atTop (nhds (l m))) (a m : ℕ) :
    Tendsto (fun j => translate a (v j) m) atTop (nhds (translate a l m)) :=
  tendsto_finsetSum _ fun i _ => (hl (m - i)).const_mul _

private theorem limit_stationary (hd : d < b) (hu : OrdinaryMomentRecurrence b d u)
    {l : ℕ → ℝ} (hl : ∀ m, Tendsto (fun j => u j m) atTop (nhds (l m))) (m : ℕ) :
    residual (range b) ((b : ℝ) ^ (m + 1)) l m = 0 := by
  have hs (k : ℕ) := (tendsto_add_atTop_iff_nat 1).mpr (hl k)
  have h : residual (digits b d) ((b : ℝ) ^ (m + 1)) l m = translate d l m := by
    refine tendsto_nhds_unique_of_eventuallyEq
      (((hs m).const_mul _).sub (tendsto_finsetSum _ fun a _ => translate_tendsto hs a m))
      (translate_tendsto hl d m) ?_
    exact Eventually.of_forall fun j => row_eq hd hu (j + 1) m
  rw [residual, ← (range b).sum_erase_add (fun a => translate a l m) (mem_range.mpr hd)]
  unfold residual at h
  linarith

private theorem limit_eq_uniform (hb : 1 < b) {l : ℕ → ℝ} (h0 : l 0 = b)
    (hl : ∀ m, residual (range b) ((b : ℝ) ^ (m + 1)) l m = 0) :
    ∀ m, l m = uniformMoment b m := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    rcases m with _ | m
    · simpa [uniformMoment] using h0
    · have he := hl (m + 1)
      have hu := uniform_stationary b (m + 1)
      have heq (a : ℕ) : lower a l (m + 1) = lower a (uniformMoment b) (m + 1) := by
        refine sum_congr rfl fun i hi => ?_
        rw [ih _ (by have := mem_Icc.mp hi; omega)]
      simp only [residual_eq, card_range, heq] at he hu
      have hp : (b : ℝ) ^ 1 < (b : ℝ) ^ (m + 1 + 1) :=
        pow_lt_pow_right₀ (by exact_mod_cast hb) (by omega)
      rw [pow_one] at hp
      exact mul_left_cancel₀ (sub_ne_zero.mpr hp.ne')
        (show ((b : ℝ) ^ (m + 1 + 1) - b) * l (m + 1) = _ by linarith only [he, hu])

private theorem moment_tendsto (hb : 1 < b) (hd : d < b) (hu : OrdinaryMomentRecurrence b d u)
    (m : ℕ) : Tendsto (fun j => u j m) atTop (nhds (uniformMoment b m)) := by
  let l (k : ℕ) := ⨆ j, u j k
  have hl (k : ℕ) : Tendsto (fun j => u j k) atTop (nhds (l k)) := by
    apply tendsto_atTop_ciSup
    · apply monotone_nat_of_le_succ
      intro j
      cases k with
      | zero => simp [degree_zero hu]
      | succ k => exact (increasing hb hd hu j _ (by omega)).le
    · refine ⟨b, ?_⟩
      rintro _ ⟨j, rfl⟩
      have ha : Antitone (u j) :=
        antitone_nat_of_succ_le fun n => sub_nonneg.mp ((gap_nonneg hb hd hu j).1 n)
      exact (ha (Nat.zero_le k)).trans_eq (degree_zero hu j)
  have h0 : l 0 = b :=
    tendsto_nhds_unique_of_eventuallyEq (hl 0) tendsto_const_nhds
      (Eventually.of_forall (degree_zero hu))
  rw [← limit_eq_uniform hb h0 (limit_stationary hd hu hl) m]
  exact hl m

end ordinaryMomentRecurrence_properties

open ordinaryMomentRecurrence_properties

/-- **Properties of solutions of the ordinary moment recurrence.** Let $b > 1$ and $d < b$ be
natural numbers, and let $(u_{j;m})_{j, m \in \mathbb{N}}$ be a family of real numbers that
satisfies the ordinary moment recurrence for $b$ and $d$. Then $u_{j;0} = b$ for every $j$, and for
all $j$ and all $m \ge 1$: $u_{j;m} \ge 0$, with $u_{j;m} = 0$ if and only if $j = 0$, $b = 2$ and
$d = 1$; $u_{j;m+1} \le u_{j;m}$, with strict inequality when $u_{j;m} \ne 0$;
$u_{j;m} < u_{j+1;m}$; and $u_{j;m} \to b/(m+1)$ as $j \to \infty$.

Source: Jean-François Burnol, *Measures for the
Summation of Irwin Series*, INTEGERS 26 (2026), Article A11, Theorem 1. -/
public theorem ordinaryMomentRecurrence_properties
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (u : ℕ → ℕ → ℝ)
    (hu : OrdinaryMomentRecurrence b d u) :
    (∀ j, u j 0 = b) ∧
    (∀ j m, 1 ≤ m →
      0 ≤ u j m ∧ (u j m = 0 ↔ j = 0 ∧ b = 2 ∧ d = 1)) ∧
    (∀ j m, 1 ≤ m →
      u j (m + 1) ≤ u j m ∧ (u j m ≠ 0 → u j (m + 1) < u j m)) ∧
    (∀ j m, 1 ≤ m → u j m < u (j + 1) m) ∧
    (∀ m, 1 ≤ m →
      Tendsto (fun j : ℕ => u j m) atTop (nhds ((b : ℝ) / (m + 1)))) := by
  exact ⟨degree_zero hu, fun j m hm => ⟨moment_nonneg hb hd hu j m,
    moment_zero_iff hb hd hu j m hm⟩, fun j m hm => ⟨sub_nonneg.mp ((gap_nonneg hb hd hu j).1 m),
    fun h => sub_pos.mp (gap_pos hb hd hu j m hm h)⟩, increasing hb hd hu,
    fun m _ => moment_tendsto hb hd hu m⟩

end MetaMathlibExt
