/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Sort
public import Mathlib.Dynamics.PeriodicPts.Defs
public import MathlibExt.NumberTheory.Digits.KaprekarProjectiveOrderTotient
import MathlibExt.NumberTheory.Digits.KaprekarStructuralClassification
import Mathlib.Tactic.NormNum

/-!
# Maximal four-digit Kaprekar periods in odd bases

We define the four-digit Kaprekar map and its state space. In odd bases `B > 3`, we
bound cycle lengths by `(B - 1) / 2` and characterize when a cycle attains this bound.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The four-digit Kaprekar map in difference coordinates.** For a base $B$ and a pair of
natural numbers $(d_1, d_2)$, the map $K_B$ forms the list of four digits
$[d_1 - 1, B - 1, B - 1, B - d_1]$ if $d_2 = 0$ and $[d_1, d_2 - 1, B - d_2 - 1, B - d_1]$ if
$d_2 > 0$, sorts it decreasingly as $a_1 \ge a_2 \ge a_3 \ge a_4$, and sets
$K_B(d_1, d_2) = (a_1 - a_4, a_2 - a_3)$. Subtraction of natural numbers is truncated at $0$;
for $1 \le d_1 < B$ and $0 \le d_2 \le d_1$ no truncation occurs.

For such $(d_1, d_2)$ the list holds the digits of the Kaprekar difference (largest minus
smallest arrangement) of any four-digit base-$B$ string with difference coordinates
$(d_1, d_2)$, as in paper displays (5) and (6).

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Section 2.1. -/
public def kaprekarFourDigitStep (B : ℕ) (d : ℕ × ℕ) : ℕ × ℕ :=
  match List.insertionSort (· ≥ ·)
    (if d.2 = 0 then [d.1 - 1, B - 1, B - 1, B - d.1]
      else [d.1, d.2 - 1, B - d.2 - 1, B - d.1]) with
  | [a, b, c, e] => (a - e, b - c)
  | _ => (0, 0)

/-- **Sample values of the four-digit Kaprekar map.** The four-digit Kaprekar map satisfies
$K_{11}(5, 1) = (9, 1)$, $K_{11}(6, 0) = (5, 5)$ and $K_{11}(5, 5) = (2, 0)$ in base $11$, and
$K_7(3, 1) = (5, 1)$, $K_7(5, 1) = (5, 3)$ and $K_7(5, 3) = (3, 1)$ in base $7$.

In particular $(3, 1) \mapsto (5, 1) \mapsto (5, 3) \mapsto (3, 1)$ is a terminal cycle of $K_7$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Examples 7, 12 and 18. -/
public theorem kaprekarFourDigitStep_examples :
    kaprekarFourDigitStep 11 (5, 1) = (9, 1) ∧ kaprekarFourDigitStep 11 (6, 0) = (5, 5) ∧
      kaprekarFourDigitStep 11 (5, 5) = (2, 0) ∧ kaprekarFourDigitStep 7 (3, 1) = (5, 1) ∧
      kaprekarFourDigitStep 7 (5, 1) = (5, 3) ∧ kaprekarFourDigitStep 7 (5, 3) = (3, 1) := by
  simp [kaprekarFourDigitStep, List.insertionSort_cons, List.orderedInsert_cons]

/-- **The four-digit Kaprekar state space.** For a base $B$, the state space $X_B$ is the finite
set of pairs of natural numbers $(d_1, d_2)$ with $1 \le d_1 < B$ and $0 \le d_2 \le d_1$.

A nonconstant four-digit base-$B$ string with sorted digits $a_1 \ge a_2 \ge a_3 \ge a_4$ has
difference coordinates $(d_1, d_2) = (a_1 - a_4, a_2 - a_3)$, a point of $X_B$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
display (2). -/
public def kaprekarFourDigitStates (B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range B ×ˢ Finset.range B).filter fun d => 1 ≤ d.1 ∧ d.2 ≤ d.1

/-- **Sizes of the Kaprekar state spaces in bases 3 and 7.** The four-digit Kaprekar state spaces
satisfy $|X_3| = 5$ and $|X_7| = 27$.

Both values agree with the general count $|X_B| = (B - 1)(B + 2)/2$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
display (2) and the proof of Corollary 27. -/
public theorem kaprekarFourDigitStates_card_examples :
    (kaprekarFourDigitStates 3).card = 5 ∧ (kaprekarFourDigitStates 7).card = 27 := by
  decide

end

open Function

namespace kaprekar_minimalPeriod_le_and_eq_iff

private def stableStates (B : ℕ) : Set (ℕ × ℕ) :=
  {d | (1 ≤ d.1 ∧ d.1 < B ∧ d.2 ≤ d.1) ∧ d.2 < d.1 ∧ 0 < d.2 ∧ Odd d.1 ∧ Odd d.2}

private theorem mem_fourDigitStates {B : ℕ} {d : ℕ × ℕ} :
    d ∈ kaprekarFourDigitStates B ↔ 1 ≤ d.1 ∧ d.1 < B ∧ d.2 ≤ d.1 := by
  simp only [kaprekarFourDigitStates, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

private theorem mem_stable_of_periodic {B : ℕ}
    (hstable : Set.MapsTo (kaprekarFourDigitStep B) (stableStates B) (stableStates B))
    (henter : Set.MapsTo (kaprekarFourDigitStep B)^[3]
      {d | 1 ≤ d.1 ∧ d.1 < B ∧ d.2 ≤ d.1} (stableStates B))
    {d : ℕ × ℕ} (hd : d ∈ kaprekarFourDigitStates B)
    (hp : d ∈ periodicPts (kaprekarFourDigitStep B)) : d ∈ stableStates B := by
  let k := minimalPeriod (kaprekarFourDigitStep B) d
  have hk : 0 < k := minimalPeriod_pos_of_mem_periodicPts hp
  have hperiod := (isPeriodicPt_minimalPeriod (kaprekarFourDigitStep B) d).mul_const 3
  have h := hstable.iterate (k * 3 - 3) (henter (mem_fourDigitStates.mp hd))
  rw [← iterate_add_apply, Nat.sub_add_cancel (by omega : 3 ≤ k * 3), hperiod.eq] at h
  exact h

private theorem minimalPeriod_eq_of_semiconj {α β : Type*} {f : α → α} {g : β → β}
    {s : Set α} (hf : Set.MapsTo f s s) {e : s → β} (he : Injective e)
    (h : Semiconj e (hf.restrict f s s) g) (x : s) :
    minimalPeriod f x.val = minimalPeriod g (e x) := by
  apply minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  change f^[n] x.val = x.val ↔ g^[n] (e x) = e x
  rw [← h.iterate_right n x, he.eq_iff, ← hf.coe_iterate_restrict x n]
  exact Subtype.ext_iff.symm

private theorem period_lt_two_in_base_five {d : ℕ × ℕ} (hd : d ∈ stableStates 5) :
    minimalPeriod (kaprekarFourDigitStep 5) d < 2 := by
  obtain ⟨a, b⟩ := d
  change (1 ≤ a ∧ a < 5 ∧ b ≤ a) ∧ b < a ∧ 0 < b ∧ Odd a ∧ Odd b at hd
  obtain ⟨⟨-, ha, -⟩, hab, hb, ⟨i, hi⟩, ⟨j, hj⟩⟩ := hd
  have h : (a, b) = (3, 1) := Prod.ext (by omega) (by omega)
  have hfixed : IsFixedPt (kaprekarFourDigitStep 5) (3, 1) := by
    simp [IsFixedPt, kaprekarFourDigitStep, List.insertionSort_cons, List.orderedInsert_cons]
  rw [h, minimalPeriod_eq_one_iff_isFixedPt.mpr hfixed]
  decide

private def double (B : ℕ) (S : Finset (Finset (ZMod B))) : Finset (Finset (ZMod B)) :=
  S.image fun C => C.image (· * 2)

private def projectiveClass {B : ℕ} (x : ZMod B) : Finset (ZMod B) := {x, -x}

private def adjacentPair {B : ℕ} (x : ZMod B) : Finset (Finset (ZMod B)) :=
  {projectiveClass x, projectiveClass (x * 2)}

private theorem iterate_adjacentPair (B n : ℕ) :
    (double B)^[n] (adjacentPair 1) = adjacentPair ((2 : ZMod B) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih, pow_succ]
    simp [double, adjacentPair, projectiveClass, neg_mul]

private theorem eq_or_eq_neg_of_class_eq {B : ℕ} {x y : ZMod B}
    (h : projectiveClass x = projectiveClass y) : x = y ∨ x = -y := by
  have hx : x ∈ projectiveClass y := h ▸ Finset.mem_insert_self _ _
  simpa [projectiveClass] using hx

private theorem natCast_ne_one_and_ne_neg_one {B k : ℕ} (hk : 1 < k) (hB : k + 1 < B) :
    (k : ZMod B) ≠ 1 ∧ (k : ZMod B) ≠ -1 := by
  constructor
  · intro h
    have hm := (ZMod.natCast_eq_natCast_iff' k 1 B).mp (by simpa only [Nat.cast_one] using h)
    rw [Nat.mod_eq_of_lt (by omega : k < B), Nat.mod_eq_of_lt (by omega : 1 < B)] at hm
    omega
  · intro h
    have hz : ((k + 1 : ℕ) : ZMod B) = 0 := by simp [h]
    exact hB.not_ge (Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff _ _).mp hz))

private theorem class_two_ne_class_one {B : ℕ} (hB7 : 7 ≤ B) :
    projectiveClass (2 : ZMod B) ≠ projectiveClass 1 := by
  intro h
  obtain ⟨hpos, hneg⟩ := natCast_ne_one_and_ne_neg_one (B := B) (k := 2) (by decide) (by omega)
  exact (eq_or_eq_neg_of_class_eq h).elim hpos hneg

private theorem adjacentPair_one_mem {B : ℕ} (hB7 : 7 ≤ B) :
    (adjacentPair (1 : ZMod B)).card = 2 ∧
      ∀ C ∈ adjacentPair (1 : ZMod B), ∃ x : ZMod B, x ≠ 0 ∧ C = {x, -x} := by
  have : Fact (1 < B) := ⟨by omega⟩
  rw [adjacentPair, one_mul]
  refine ⟨by simp [(class_two_ne_class_one hB7).symm], ?_⟩
  intro C hC
  simp only [Finset.mem_insert, Finset.mem_singleton] at hC
  rcases hC with rfl | rfl
  · exact ⟨1, one_ne_zero, rfl⟩
  · refine ⟨2, ?_, rfl⟩
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 2) ((ZMod.natCast_eq_zero_iff 2 B).mp h)
    omega

private theorem period_adjacentPair_eq_projectiveOrderTwo {B : ℕ} (hB : Odd B)
    (hB7 : 7 ≤ B) : minimalPeriod (double B) (adjacentPair 1) = projectiveOrderTwo B := by
  let n := minimalPeriod (double B) (adjacentPair 1)
  obtain ⟨hn, hupper⟩ := projective_doubling_minimalPeriod_le_projectiveOrderTwo B hB
    (by omega) _ (adjacentPair_one_mem hB7)
  have hfix := iterate_minimalPeriod (f := double B) (x := adjacentPair 1)
  rw [iterate_adjacentPair] at hfix
  let a : ZMod B := 2 ^ n
  change adjacentPair a = adjacentPair 1 at hfix
  have hmem {C : Finset (ZMod B)} (hC : C ∈ adjacentPair (1 : ZMod B)) :
      C = projectiveClass a ∨ C = projectiveClass (a * 2) := by
    rw [← hfix] at hC
    simpa only [adjacentPair, Finset.mem_insert, Finset.mem_singleton] using hC
  have h1 : projectiveClass (1 : ZMod B) ∈ adjacentPair 1 := by simp [adjacentPair]
  refine le_antisymm hupper (Nat.sInf_le ⟨hn, ?_⟩)
  rcases hmem h1 with h1 | h1
  · exact eq_or_eq_neg_of_class_eq h1.symm
  · -- Swapping the two classes would make 4 congruent to 1 or -1.
    have h2 : projectiveClass (2 : ZMod B) ∈ adjacentPair 1 := by simp [adjacentPair]
    have ha2 := eq_or_eq_neg_of_class_eq
      ((hmem h2).resolve_right (fun h => class_two_ne_class_one hB7 (h.trans h1.symm))).symm
    have ha1 := eq_or_eq_neg_of_class_eq h1.symm
    obtain ⟨hpos, hneg⟩ :=
      natCast_ne_one_and_ne_neg_one (B := B) (k := 4) (by decide) (by omega)
    exfalso
    rcases ha2 with ha | ha
    · rw [ha, show (2 : ZMod B) * 2 = 4 by norm_num] at ha1
      exact ha1.elim hpos hneg
    · rw [ha, neg_mul, show (2 : ZMod B) * 2 = 4 by norm_num] at ha1
      exact ha1.elim (fun h => hneg (neg_eq_iff_eq_neg.mp h))
        (fun h => hpos (neg_injective h))

end kaprekar_minimalPeriod_le_and_eq_iff

open kaprekar_minimalPeriod_le_and_eq_iff

/-- **Maximal Kaprekar cycle length in odd bases.** Let $B > 3$ be odd, let $K_B$ be the
four-digit Kaprekar map and $X_B$ its state space, and let $\lambda(B)$ be the projective order
of $2$ modulo $B$. Every point of $X_B$ that is periodic for $K_B$ has minimal period at most
$(B - 1)/2$. Moreover, some point of $X_B$ has minimal period exactly $(B - 1)/2$ under $K_B$
if and only if $B \ge 7$, $B$ is prime and $\lambda(B) = (B - 1)/2$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Corollary 3 (`jis-2026-26.4.7-cor-3`). -/
public theorem kaprekar_minimalPeriod_le_and_eq_iff (B : ℕ) (hB : Odd B)
    (hB3 : 3 < B) :
    (∀ d ∈ kaprekarFourDigitStates B, d ∈ Function.periodicPts (kaprekarFourDigitStep B) →
      Function.minimalPeriod (kaprekarFourDigitStep B) d ≤ (B - 1) / 2) ∧
      ((∃ d ∈ kaprekarFourDigitStates B,
          Function.minimalPeriod (kaprekarFourDigitStep B) d = (B - 1) / 2) ↔
        7 ≤ B ∧ B.Prime ∧ projectiveOrderTwo B = (B - 1) / 2) := by
  obtain ⟨hstable, henter, -, -, e, he, hconj⟩ :=
    four_digit_kaprekar_structural_classification B hB hB3
  have hperiod (d : stableStates B) :
      minimalPeriod (kaprekarFourDigitStep B) d.val =
        minimalPeriod (double B) (e d).val := by
    apply minimalPeriod_eq_of_semiconj hstable (e := fun x => (e x).val)
      (fun _ _ h => e.injective (Subtype.ext h)) _ d
    intro x
    exact (hconj x).trans (congrArg (double B) (he x).symm)
  have horder {d : ℕ × ℕ} (hd : d ∈ kaprekarFourDigitStates B)
      (hp : d ∈ periodicPts (kaprekarFourDigitStep B)) :
      minimalPeriod (kaprekarFourDigitStep B) d ≤ projectiveOrderTwo B := by
    let x : stableStates B := ⟨d, mem_stable_of_periodic hstable henter hd hp⟩
    exact (hperiod x).le.trans
      (projective_doubling_minimalPeriod_le_projectiveOrderTwo B hB hB3 _ (e x).property).2
  have htot := projectiveOrderTwo_le_totient_div_two B hB hB3
  have htot_lt := Nat.totient_lt B (by omega)
  have hbound : projectiveOrderTwo B ≤ (B - 1) / 2 := by omega
  refine ⟨fun d hd hp => (horder hd hp).trans hbound, ?_⟩
  constructor
  · rintro ⟨d, hd, hmax⟩
    have hp : d ∈ periodicPts (kaprekarFourDigitStep B) :=
      minimalPeriod_pos_iff_mem_periodicPts.mp (by omega)
    have hlarge : 7 ≤ B := by
      by_contra! hsmall
      have hfive : B = 5 := by obtain ⟨k, hk⟩ := hB; omega
      subst B
      exact (period_lt_two_in_base_five (mem_stable_of_periodic hstable henter hd hp)).ne hmax
    have hle := horder hd hp
    have hprime : B.Prime := (Nat.totient_eq_iff_prime (by omega)).mp (by
      obtain ⟨k, hk⟩ := hB
      omega)
    exact ⟨hlarge, hprime, by omega⟩
  · rintro ⟨hlarge, -, hmax⟩
    let d : stableStates B := e.symm ⟨adjacentPair (1 : ZMod B), adjacentPair_one_mem hlarge⟩
    have hs : (e d).val = adjacentPair (1 : ZMod B) := by
      exact congrArg Subtype.val (e.apply_symm_apply _)
    refine ⟨d.val, mem_fourDigitStates.mpr d.property.1, ?_⟩
    rw [hperiod d, hs, period_adjacentPair_eq_projectiveOrderTwo hB hlarge, hmax]

end MetaMathlibExt
