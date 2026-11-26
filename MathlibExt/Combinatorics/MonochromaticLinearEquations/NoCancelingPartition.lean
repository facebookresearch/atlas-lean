/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.MonochromaticLinearEquations.Recolouring
import all MathlibExt.Combinatorics.MonochromaticLinearEquations.Recolouring
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Even-length equations without a canceling partition

An equation of even length at least four, with nonzero coefficients of both signs and no
canceling partition, is uncommon over the integers for every palette of at least two colours.

For two colours, take a trigonometric polynomial supported on the coefficients and their
negatives. Choose its phases so that their product along the equation is negative. On tuples
satisfying no second independent equation from the finite spectrum, averaging over dilations
leaves only the zero vector and the two signs of the coefficient vector. The exceptional tuples
and the tuples with repeated coordinates have density tending to zero among the solutions.
Independent colour choices then give a deterministic colouring with a fixed deficit.

This two-colour construction adapts the Fourier-analytic proofs that such equations are not
common over finite fields (Fox, Pham and Zhao) and over finite abelian groups whose order is
coprime to the coefficients (Versteegen). As in Versteegen's proof, the frequencies are the
coefficients and their negatives (there multiplied by an element of maximal order), and the
phases are chosen using a value whose multiplicity among the coefficients differs from that of
its negative, which exists because there is no canceling partition. Wijaya's paper takes the
two-colour case over the integers from Versteegen's theorem (arXiv:2501.17136, Section 1.2,
through its Lemma 3.1).

## References

* J. Fox, H. T. Pham and Y. Zhao, *Common and Sidorenko linear equations*, Q. J. Math. 72
  (2021), 1223–1234 (arXiv:1910.06436, Theorem 1.4(b)).
* L. Versteegen, *Common and Sidorenko equations in Abelian groups*, J. Comb. 14 (2023),
  53–67 (arXiv:2109.04445, Theorem 1.4(iv)).
* L. P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least Three Colors*,
  INTEGERS 25 (2025), Article A88 (arXiv:2501.17136).
-/

namespace MetaMathlibExt
namespace isUncommonOverIntegers_of_not_hasCancelingPartition

open Finset Filter Complex
open scoped ComplexConjugate
open isUncommonOverIntegers_of_two

private def skew (d z : ℤ) : ℤ := (if z = d then 1 else 0) - (if z = -d then 1 else 0)

private lemma skew_neg (d z : ℤ) : skew d (-z) = -skew d z := by
  simp only [skew, neg_eq_iff_eq_neg, neg_neg]
  ring

-- Matching the two fibres of each absolute value gives a fixed-point-free involution.
private lemma imbalance {k : ℕ} (a : Fin k → ℤ) (ha : ∀ i, a i ≠ 0)
    (h : ¬ HasCancelingPartition a) : ∃ d : ℤ, ∑ i, skew d (a i) ≠ 0 := by
  classical
  by_contra! hz
  apply h
  have eqv (d : ℤ) : Nonempty ({i // a i = d} ≃ {i // a i = -d}) := by
    apply Fintype.card_eq.mp
    have hd := hz d
    simp only [skew, sum_sub_distrib, sum_boole, sub_eq_zero] at hd
    simpa [Fintype.card_subtype] using hd
  let e (d : ℤ) := (eqv d).some
  let L (d : ℤ) (i : Fin k) := if hi : a i = d then (e d ⟨i, hi⟩).val else i
  let R (d : ℤ) (i : Fin k) := if hi : a i = -d then ((e d).symm ⟨i, hi⟩).val else i
  have hL {d i} (hi : a i = d) : a (L d i) = -d := by
    simpa only [L, dite_eq_left hi] using (e d ⟨i, hi⟩).property
  have hR {d i} (hi : a i = -d) : a (R d i) = d := by
    simpa only [R, dite_eq_left hi] using ((e d).symm ⟨i, hi⟩).property
  have RL {d i} (hi : a i = d) : R d (L d i) = i := by
    simp only [R, dite_eq_left (e d ⟨i, hi⟩).property, L, dite_eq_left hi, Subtype.coe_eta,
      Equiv.symm_apply_apply]
  have LR {d i} (hi : a i = -d) : L d (R d i) = i := by
    simp only [L, dite_eq_left ((e d).symm ⟨i, hi⟩).property, R, dite_eq_left hi,
      Subtype.coe_eta, Equiv.apply_symm_apply]
  let f (i : Fin k) := if 0 < a i then L (a i) i else R (-a i) i
  have hf (i) : a (f i) = -a i := by
    dsimp only [f]
    split
    · exact hL rfl
    · exact hR (neg_neg _).symm
  have inv (i) : f (f i) = i := by
    change (if 0 < a (f i) then L (a (f i)) (f i) else R (-a (f i)) (f i)) = i
    rw [hf, neg_neg]
    by_cases hp : 0 < a i
    · simpa [f, hp, not_lt_of_ge hp.le] using (RL (d := a i) (i := i) rfl)
    · have hn : a i < 0 := lt_of_le_of_ne (le_of_not_gt hp) (ha i)
      simpa [f, hp, hn] using (LR (d := -a i) (i := i) (neg_neg _).symm)
  refine ⟨⟨f, f, inv, inv⟩, inv, fun i hi => ha i ?_, fun i => ?_⟩
  · have he := hf i
    change f i = i at hi
    rw [hi] at he
    omega
  · change a i + a (f i) = 0
    simp [hf]

-- A phase of π divided by the imbalance contributes a total phase of π.
private lemma phases {k : ℕ} (a : Fin k → ℤ) (ha : ∀ i, a i ≠ 0)
    (h : ¬ HasCancelingPartition a) :
    ∃ u : ℤ → ℂ, (∀ z, ‖u z‖ = 1) ∧ (∀ z, u (-z) = conj (u z)) ∧ ∏ i, u (a i) = -1 := by
  obtain ⟨d, hd⟩ := imbalance a ha h
  let D : ℤ := ∑ i, skew d (a i)
  let θ : ℝ := Real.pi / D
  refine ⟨fun z => Complex.exp (((skew d z : ℝ) * θ : ℝ) * I), fun z =>
    norm_exp_ofReal_mul_I _, fun z => ?_, ?_⟩
  · dsimp only
    rw [← Complex.exp_conj, skew_neg]
    push_cast
    simp [mul_assoc]
  · rw [← Complex.exp_sum, ← sum_mul]
    push_cast
    rw [← sum_mul]
    have hD : (D : ℂ) ≠ 0 := by exact_mod_cast hd
    have he : (∑ i, (skew d (a i) : ℂ)) = (D : ℂ) := by simp [D]
    rw [he]
    simp only [θ, ofReal_div, ofReal_intCast]
    rw [show (D : ℂ) * (↑Real.pi / ↑D) = ↑Real.pi by field_simp, Complex.exp_pi_mul_I]

private def freq {k : ℕ} (a : Fin k → ℤ) : Finset ℤ :=
  univ.image a ∪ univ.image (-a)

private lemma mem_freq {k : ℕ} {a : Fin k → ℤ} {z : ℤ} :
    z ∈ freq a ↔ ∃ i, z = a i ∨ z = -a i := by
  simp [freq, eq_comm, exists_or]

private abbrev dot {k : ℕ} (a x : Fin k → ℤ) := ∑ i, a i * x i

-- A nonzero proportional frequency vector in the spectrum has scale ±1:
-- test the scale at the smallest and largest absolute coefficient.
private lemma independent {k : ℕ} (a b : Fin k → ℤ) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, b i ∈ insert 0 (freq a)) (h₀ : b ≠ 0) (h₁ : b ≠ a) (h₂ : b ≠ -a) :
    ∃ i j, a i * b j ≠ a j * b i := by
  classical
  by_contra! h
  obtain ⟨t, ht⟩ : ∃ t, b t ≠ 0 := by simpa [funext_iff] using h₀
  have hn (i) : b i ≠ 0 := fun he => by
    have := h i t
    rw [he, mul_zero] at this
    exact (mul_ne_zero (ha i) ht) this
  have hf (i) : ∃ j, |b i| = |a j| := by
    obtain ⟨j, hj | hj⟩ := mem_freq.mp ((mem_insert.mp (hb i)).resolve_left (hn i))
    all_goals exact ⟨j, by simp [hj]⟩
  have habs (i) := congrArg abs (h i t)
  simp only [abs_mul] at habs
  obtain ⟨lo, -, hlo⟩ := exists_min_image univ (fun i => |a i|) ⟨t, mem_univ _⟩
  obtain ⟨hi, -, hhi⟩ := exists_max_image univ (fun i => |a i|) ⟨t, mem_univ _⟩
  obtain ⟨j, hj⟩ := hf lo
  obtain ⟨l, hl⟩ := hf hi
  have hlower : |a t| ≤ |b t| := by
    apply le_of_mul_le_mul_left (a := |a lo|) _ (abs_pos.mpr (ha lo))
    rw [habs, hj, mul_comm]
    exact mul_le_mul_of_nonneg_left (hlo j (mem_univ _)) (abs_nonneg _)
  have hupper : |b t| ≤ |a t| := by
    apply le_of_mul_le_mul_left (a := |a hi|) _ (abs_pos.mpr (ha hi))
    rw [habs, hl, mul_comm |a t|]
    exact mul_le_mul_of_nonneg_right (hhi l (mem_univ _)) (abs_nonneg _)
  rcases abs_eq_abs.mp (le_antisymm hupper hlower) with he | he
  · apply h₁
    funext i
    exact mul_left_cancel₀ (ha t) (by rw [← h, he, mul_comm])
  · apply h₂
    funext i
    apply mul_left_cancel₀ (ha t)
    rw [← h, he]
    simp [mul_comm]

-- On the intersection of two independent equations, all but two coordinates
-- determine the tuple.
private lemma two_forms_le {k : ℕ} (a b : Fin k → ℤ) (i j : Fin k)
    (hdet : a i * b j ≠ a j * b i) (n : ℕ) :
    ((solutions a n).filter (fun x => dot b x = 0)).card ≤ n ^ (k - 2) := by
  classical
  have hij : j ≠ i := by rintro rfl; exact hdet rfl
  let keep := (univ.erase i).erase j
  let box := Fintype.piFinset fun _ : keep => Icc (1 : ℤ) n
  have hc : box.card = n ^ (k - 2) := by
    simp [box, keep, Fintype.card_piFinset, card_erase_of_mem, hij, Nat.sub_sub, Int.card_Icc]
  rw [← hc]
  apply card_le_card_of_injOn (fun (x : Fin k → ℤ) (t : keep) => x t)
  · intro x hx
    exact Fintype.mem_piFinset.mpr fun t =>
      mem_Icc.mpr ((mem_solutions.mp (mem_filter.mp hx).1).1 t)
  · intro x hx y hy hxy
    have diff (c : Fin k → ℤ) (he : dot c x = dot c y) :
        c i * (x i - y i) + c j * (x j - y j) = 0 := by
      have hh : ∑ t ∈ keep, c t * x t = ∑ t ∈ keep, c t * y t :=
        sum_congr rfl fun t ht => by rw [show x t = y t from congrFun hxy ⟨t, ht⟩]
      have split (u : Fin k → ℤ) : dot c u = ∑ t ∈ keep, c t * u t + c j * u j + c i * u i := by
        rw [sum_erase_add _ _ (mem_erase.mpr ⟨hij, mem_univ _⟩), sum_erase_add _ _ (mem_univ i)]
      rw [split x, split y, hh] at he
      linarith only [he]
    have e := diff a ((mem_solutions.mp (mem_filter.mp hx).1).2.trans
      (mem_solutions.mp (mem_filter.mp hy).1).2.symm)
    have f := diff b ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
    have hne := sub_ne_zero.mpr hdet
    have hi : x i - y i = 0 := (mul_eq_zero.mp (show
      (a i * b j - a j * b i) * (x i - y i) = 0 by
        linear_combination b j * e - a j * f)).resolve_left hne
    have hj : x j - y j = 0 := (mul_eq_zero.mp (show
      (a i * b j - a j * b i) * (x j - y j) = 0 by
        linear_combination a i * f - b i * e)).resolve_left hne
    funext t
    by_cases ht : t = i
    · simpa [ht] using sub_eq_zero.mp hi
    by_cases ht' : t = j
    · simpa [ht'] using sub_eq_zero.mp hj
    exact congrFun hxy ⟨t, by simp [keep, ht, ht']⟩

private def vectors {k : ℕ} (a : Fin k → ℤ) :=
  Fintype.piFinset fun _ : Fin k => insert 0 (freq a)

private def exceptional {k : ℕ} (a : Fin k → ℤ) :=
  (vectors a).filter fun b => b ≠ 0 ∧ b ≠ a ∧ b ≠ -a

private lemma positive_solution {k : ℕ} (a : Fin k → ℤ) (hs : ∃ i j, a i < 0 ∧ 0 < a j) :
    ∃ b : Fin k → ℤ, (∀ i, 0 < b i) ∧ dot a b = 0 := by
  obtain ⟨i, j, hi, hj⟩ := hs
  let P := ∑ t, max (a t) 0
  let N := ∑ t, max (-a t) 0
  have hP : 0 < P := (lt_max_of_lt_left hj).trans_le
    (single_le_sum (fun t _ => le_max_right (a t) 0) (mem_univ j))
  have hN : 0 < N := (lt_max_of_lt_left (neg_pos.mpr hi)).trans_le
    (single_le_sum (fun t _ => le_max_right (-a t) 0) (mem_univ i))
  let b (t : Fin k) := if 0 < a t then N else P
  refine ⟨b, fun t => by dsimp [b]; split <;> assumption, ?_⟩
  have term (t) : a t * b t = max (a t) 0 * N - max (-a t) 0 * P := by
    by_cases ht : 0 < a t
    · simp [b, ht, max_eq_left ht.le, max_eq_right (neg_nonpos.mpr ht.le)]
    · simp [b, ht, max_eq_right (le_of_not_gt ht), max_eq_left (neg_nonneg.mpr (le_of_not_gt ht))]
  simp only [dot, term, sum_sub_distrib, ← sum_mul]
  change P * N - N * P = 0
  ring

open Classical in
private noncomputable def bad {k : ℕ} (a : Fin k → ℤ) (n : ℕ) :=
  repeats (solutions a n) ∪
    (exceptional a).biUnion (fun b => (solutions a n).filter (fun x => dot b x = 0))

private lemma bad_le {k : ℕ} (hk : 3 ≤ k) (a : Fin k → ℤ) (ha : ∀ i, a i ≠ 0) (n : ℕ) :
    (bad a n).card ≤ (k ^ 2 + (exceptional a).card) * n ^ (k - 2) := by
  classical
  apply (card_union_le ..).trans
  rw [add_mul]
  apply Nat.add_le_add (repeats_le hk a ha n)
  apply card_biUnion_le.trans
  rw [← Nat.nsmul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro b hb
  obtain ⟨hv, h₀, h₁, h₂⟩ := mem_filter.mp hb
  obtain ⟨i, j, hij⟩ := independent a b ha (Fintype.mem_piFinset.mp hv) h₀ h₁ h₂
  exact two_forms_le a b i j hij n

private lemma large_interval {k : ℕ} (hk : 3 ≤ k) (a : Fin k → ℤ) (ha : ∀ i, a i ≠ 0)
    (hs : ∃ i j, a i < 0 ∧ 0 < a j) (Q n₀ : ℕ) :
    ∃ n ≥ n₀, 0 < (solutions a n).card ∧ Q * (bad a n).card ≤ (solutions a n).card := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 2 := ⟨k - 2, by omega⟩
  obtain ⟨b, hb, he⟩ := positive_solution a hs
  obtain ⟨C, hC, hmany⟩ := many_solutions a b (by omega) (ha 0) hb he
  let B := (d + 2) ^ 2 + (exceptional a).card
  let m := max n₀ (Q * B * C ^ d) + 1
  have hm : 0 < m := Nat.succ_pos _
  have hlo : n₀ ≤ C * m := (show n₀ ≤ m by dsimp [m]; omega).trans
    (Nat.le_mul_of_pos_left m hC)
  refine ⟨C * m, hlo, (pow_pos hm _).trans_le (hmany m), ?_⟩
  have hbad : (bad a (C * m)).card ≤ B * (C * m) ^ d := by
    simpa [B] using bad_le hk a ha (C * m)
  calc
    _ ≤ Q * (B * (C * m) ^ d) := Nat.mul_le_mul_left Q hbad
    _ = (Q * B * C ^ d) * m ^ d := by rw [mul_pow]; ring
    _ ≤ m * m ^ d := Nat.mul_le_mul_right _ (by dsimp [m]; omega)
    _ = m ^ (d + 1) := (pow_succ' m d).symm
    _ ≤ _ := hmany m

private noncomputable def wave {k q : ℕ} [NeZero q] (a : Fin k → ℤ) (u : ℤ → ℂ)
    (t : ZMod q) (z : ℤ) : ℂ :=
  ∑ j ∈ freq a, u j * ZMod.stdAddChar (t * ((j * z : ℤ) : ZMod q))

private lemma char_norm {q : ℕ} [NeZero q] (t : ZMod q) : ‖ZMod.stdAddChar t‖ = 1 := by
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

private lemma wave_real {k q : ℕ} [NeZero q] (a : Fin k → ℤ) (u : ℤ → ℂ)
    (hu : ∀ z, u (-z) = conj (u z)) (t : ZMod q) (z : ℤ) :
    ((wave a u t z).re : ℂ) = wave a u t z := by
  apply conj_eq_iff_re.mp
  rw [wave, map_sum]
  have neg_mem (j) (hj : j ∈ freq a) : -j ∈ freq a := by
    obtain ⟨i, rfl | rfl⟩ := mem_freq.mp hj
    · exact mem_freq.mpr ⟨i, Or.inr rfl⟩
    · exact mem_freq.mpr ⟨i, Or.inl (neg_neg _)⟩
  apply sum_nbij' Neg.neg Neg.neg neg_mem neg_mem (fun _ _ => neg_neg _) (fun _ _ => neg_neg _)
  intro j _
  simp [hu, AddChar.map_neg_eq_inv, Complex.inv_eq_conj (char_norm _)]

private lemma wave_bound {k q : ℕ} [NeZero q] (a : Fin k → ℤ) (u : ℤ → ℂ)
    (hu : ∀ z, ‖u z‖ = 1) (t : ZMod q) (z : ℤ) : |(wave a u t z).re| ≤ (freq a).card := by
  refine (abs_re_le_norm _).trans ((norm_sum_le ..).trans ?_)
  simp [hu]

private lemma char_prod {q : ℕ} [NeZero q] {ι : Type*} (s : Finset ι)
    (f : ι → ZMod q) : ∏ i ∈ s, ZMod.stdAddChar (f i) = ZMod.stdAddChar (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s h ih => simp [h, ih, AddChar.map_add_eq_mul]

-- Orthogonality keeps just the constant term and the two copies of the original equation.
private lemma wave_moment {k q : ℕ} [NeZero q] [Nonempty (Fin k)]
    (a x : Fin k → ℤ) (ha : ∀ i, a i ≠ 0) (u : ℤ → ℂ)
    (hu : ∀ z, u (-z) = conj (u z)) (hprod : ∏ i, u (a i) = -1) (s : ℝ)
    (hx : ∀ b ∈ vectors a, ((dot b x : ℤ) : ZMod q) = 0 ↔ b = 0 ∨ b = a ∨ b = -a) :
    ∑ t : ZMod q, ∏ i, (1 / 2 + s * (wave a u t (x i)).re) =
      (q : ℝ) * ((1 / 2) ^ k - 2 * s ^ k) := by
  classical
  let w (j : ℤ) : ℂ := if j = 0 then 1 / 2 else s * u j
  have hzero : 0 ∉ freq a := by
    rintro h
    obtain ⟨i, hi | hi⟩ := mem_freq.mp h <;> exact ha i (by omega)
  have expan (t : ZMod q) (z : ℤ) :
      ((1 / 2 + s * (wave a u t z).re : ℝ) : ℂ) =
        ∑ j ∈ insert 0 (freq a), w j * ZMod.stdAddChar (t * ((j * z : ℤ) : ZMod q)) := by
    rw [sum_insert hzero]
    push_cast
    rw [wave_real a u hu, wave, mul_sum]
    simp only [w, ite_eq_left, zero_mul, mul_zero, AddChar.map_zero_eq_one, mul_one]
    congr 1
    apply sum_congr rfl
    intro i hi
    have hn : i ≠ 0 := fun he => hzero (he ▸ hi)
    simp [hn, mul_assoc]
  let c (b : Fin k → ℤ) := ∏ i, w (b i)
  have term (t : ZMod q) (b : Fin k → ℤ) :
      (∏ i, (w (b i) * ZMod.stdAddChar (t * ((b i * x i : ℤ) : ZMod q)))) =
        c b * ZMod.stdAddChar (t * ((dot b x : ℤ) : ZMod q)) := by
    rw [prod_mul_distrib, char_prod, ← mul_sum]
    simp [dot, c]
  let core : Finset (Fin k → ℤ) := {0, a, -a}
  have hc (b) : b ∈ core ↔ b = 0 ∨ b = a ∨ b = -a := by simp [core]
  have sub : core ⊆ vectors a := by
    intro b hb
    apply Fintype.mem_piFinset.mpr
    intro i
    rcases (hc b).mp hb with rfl | rfl | rfl
    · exact mem_insert_self ..
    · exact mem_insert_of_mem (mem_freq.mpr ⟨i, Or.inl rfl⟩)
    · exact mem_insert_of_mem (mem_freq.mpr ⟨i, Or.inr rfl⟩)
  have heq : (vectors a).filter (fun b => ((dot b x : ℤ) : ZMod q) = 0) = core := by
    ext b
    constructor
    · intro h
      obtain ⟨hb, h⟩ := mem_filter.mp h
      exact (hc b).mpr ((hx b hb).mp h)
    · intro h
      exact mem_filter.mpr ⟨sub h, (hx b (sub h)).mpr ((hc b).mp h)⟩
  have h₀ (i : Fin k) : a ≠ 0 ∧ -a ≠ 0 ∧ a ≠ -a := by
    refine ⟨fun e => ha i (congrFun e i), fun e => ha i ?_, fun e => ha i ?_⟩
    all_goals
      have h := congrFun e i
      simp only [Pi.neg_apply, Pi.zero_apply] at h
      omega
  obtain ⟨h₁, h₂, h₃⟩ := h₀ (Classical.arbitrary (Fin k))
  have cp : c a = -(s : ℂ) ^ k := by simp [c, w, ha, prod_mul_distrib, hprod]
  have cn : c (-a) = -(s : ℂ) ^ k := by
    simpa [c, w, ha, hu, prod_mul_distrib, ← map_prod] using
      congrArg (fun y : ℂ => (s : ℂ) ^ k * conj y) hprod
  have base : c 0 = (1 / 2 : ℂ) ^ k := by simp [c, w]
  have hs : ∑ b ∈ core, c b = (1 / 2 : ℂ) ^ k - 2 * s ^ k := by
    simp [core, Ne.symm h₁, Ne.symm h₂, h₃, base, cp, cn]
    ring
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_prod]
  simp_rw [expan, prod_univ_sum, term]
  rw [sum_comm]
  change (∑ b ∈ vectors a, ∑ t : ZMod q, c b * ZMod.stdAddChar (t * (dot b x : ZMod q))) = _
  simp_rw [← mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
  simp only [Nat.cast_ite, ZMod.card, Nat.cast_zero, mul_ite, mul_zero, ← sum_filter, heq,
    ← sum_mul, hs]
  push_cast
  ring

-- Product weights describe independent choices of colour at distinct integers.
private lemma fixed_colour {V : Type*} [Fintype V] [DecidableEq V] {k r : ℕ}
    (p : V → Fin r → ℝ) (hs : ∀ v, ∑ c, p v c = 1) (x : Fin k → V)
    (hx : Function.Injective x) (c : Fin r) :
    (∑ f : V → Fin r, if ∀ i, f (x i) = c then ∏ v, p v (f v) else 0) =
      ∏ i, p (x i) c := by
  classical
  let S := univ.image x
  have equiv (f : V → Fin r) : (∀ i, f (x i) = c) ↔ ∀ v, v ∈ S → f v = c := by
    simp [S]
  let g (v : V) (j : Fin r) := if v ∈ S → j = c then p v j else 0
  have factor (f : V → Fin r) :
      (if ∀ i, f (x i) = c then ∏ v, p v (f v) else 0) = ∏ v, g v (f v) := by
    simp only [g, Fintype.prod_ite_zero, equiv]
  have total (v : V) : ∑ j, g v j = if v ∈ S then p v c else 1 := by
    by_cases h : v ∈ S <;> simp [g, h, hs]
  simp_rw [factor]
  rw [← Fintype.prod_sum]
  simp_rw [total]
  rw [Fintype.prod_ite_mem, prod_image hx.injOn]

private lemma round_good {k r : ℕ} [Nonempty (Fin k)] [NeZero r] (n : ℕ)
    (G : Finset (Fin k → ℤ))
    (hrange : ∀ x ∈ G, ∀ i, x i ∈ Icc (1 : ℤ) n) (hinj : ∀ x ∈ G, Function.Injective x)
    (w : ℤ → Fin r → ℝ) (hw : ∀ z c, 0 ≤ w z c) (hs : ∀ z, ∑ c, w z c = 1) :
    ∃ χ : ℤ → Fin r, ((G.filter (mono χ)).card : ℝ) ≤ ∑ x ∈ G, ∑ c, ∏ i, w (x i) c := by
  classical
  let V := ↥(Icc (1 : ℤ) n)
  let colour (f : V → Fin r) (z : ℤ) := if h : z ∈ Icc (1 : ℤ) n then f ⟨z, h⟩ else 0
  let p (v : V) (c : Fin r) := w v c
  let mass (f : V → Fin r) := ∏ v, p v (f v)
  have hmass : ∑ f, mass f = 1 := by
    simp [mass, ← Fintype.prod_sum, p, hs]
  have hn (f) : 0 ≤ mass f := prod_nonneg fun _ _ => hw _ _
  have point (x) (hx : x ∈ G) :
      (∑ f, if mono (colour f) x then mass f else 0) = ∑ c, ∏ i, w (x i) c := by
    let y (i : Fin k) : V := ⟨x i, hrange x hx i⟩
    have hy : Function.Injective y := fun i j e => hinj x hx (congrArg Subtype.val e)
    have hsum (c : Fin r) := fixed_colour p (fun v => hs v) y hy c
    rw [← sum_congr rfl (fun c _ => hsum c), sum_comm]
    apply sum_congr rfl
    intro f _
    let c₀ := f (y (Classical.arbitrary (Fin k)))
    have he (i) : colour f (x i) = f (y i) := by simp only [colour, dite_eq_left (hrange x hx i), y]
    by_cases hm : mono (colour f) x
    · have hall (i) : f (y i) = c₀ := by simpa only [he] using hm i (Classical.arbitrary (Fin k))
      rw [ite_eq_left hm]
      simp [hall, mass]
    · have none (c : Fin r) : ¬ ∀ i, f (y i) = c := fun h => hm fun i j => by simp [he, h]
      simp [hm, none]
  let M (f) : ℝ := (G.filter (mono (colour f))).card
  have avg : ∑ f, mass f * M f = ∑ x ∈ G, ∑ c, ∏ i, w (x i) c := by
    simp only [M, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum,
      mul_ite, mul_one, mul_zero]
    rw [sum_comm]
    exact sum_congr rfl point
  obtain ⟨f, -, hf⟩ := exists_min_image univ M univ_nonempty
  refine ⟨colour f, ?_⟩
  calc
    M f = (∑ g, mass g) * M f := by rw [hmass, one_mul]
    _ ≤ ∑ g, mass g * M g := by
      rw [sum_mul]
      exact sum_le_sum fun g hg => mul_le_mul_of_nonneg_left (hf g hg) (hn g)
    _ = _ := avg

-- Choose the averaging modulus after the interval, so no extra frequency vanishes modulo it.
private lemma good_modulus {k : ℕ} (a : Fin k → ℤ) (n : ℕ) :
    ∃ q : ℕ, 0 < q ∧ ∀ x ∈ solutions a n \ bad a n, ∀ b ∈ vectors a,
      ((dot b x : ℤ) : ZMod q) = 0 ↔ b = 0 ∨ b = a ∨ b = -a := by
  classical
  let s := solutions a n
  let q := (∑ x ∈ s, ∑ b ∈ vectors a, (dot b x).natAbs) + 1
  refine ⟨q, Nat.succ_pos _, fun x hx b hb => ?_⟩
  obtain ⟨hs, hg⟩ := mem_sdiff.mp hx
  have hl : (dot b x).natAbs < q := Nat.lt_succ_of_le <|
    (single_le_sum (f := fun b => (dot b x).natAbs) (fun _ _ => Nat.zero_le _) hb).trans
      (single_le_sum (f := fun x => ∑ b ∈ vectors a, (dot b x).natAbs)
        (fun _ _ => Nat.zero_le _) hs)
  have he := (mem_solutions.mp hs).2
  constructor
  · intro hz
    have hz' := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz) (by simpa using hl : _ < (q : ℤ).natAbs)
    by_contra! h
    exact hg (mem_union_right _ (mem_biUnion.mpr ⟨b, mem_filter.mpr ⟨hb, h⟩,
      mem_filter.mpr ⟨hs, hz'⟩⟩))
  · rintro (rfl | rfl | rfl)
    · simp [dot]
    · rw [show dot b x = 0 from he, Int.cast_zero]
    · have hneg : dot (-a) x = 0 := by
        simp only [dot, Pi.neg_apply, neg_mul, sum_neg_distrib, he, neg_zero]
      rw [hneg, Int.cast_zero]

private lemma colour_good {k : ℕ} [Nonempty (Fin k)] (hk : Even k) (a : Fin k → ℤ)
    (ha : ∀ i, a i ≠ 0) (u : ℤ → ℂ) (hun : ∀ z, ‖u z‖ = 1)
    (hu : ∀ z, u (-z) = conj (u z)) (hp : ∏ i, u (a i) = -1)
    (δ : ℝ) (hδ : 0 ≤ δ) (hsmall : δ * (freq a).card ≤ 1 / 2) (n : ℕ) :
    let G := solutions a n \ bad a n
    ∃ χ : ℤ → Fin 2, ((G.filter (mono χ)).card : ℝ) ≤
      G.card * (2 * (1 / 2) ^ k - 4 * δ ^ k) := by
  classical
  let G := solutions a n \ bad a n
  obtain ⟨q, hq, hmod⟩ := good_modulus a n
  let : NeZero q := ⟨hq.ne'⟩
  let s (c : Fin 2) := if c = 0 then δ else -δ
  let w (t : ZMod q) (z : ℤ) (c : Fin 2) := 1 / 2 + s c * (wave a u t z).re
  have hw (t z c) : 0 ≤ w t z c := by
    have h := abs_le.mp (wave_bound a u hun t z)
    have hl := mul_le_mul_of_nonneg_left h.1 hδ
    have hr := mul_le_mul_of_nonneg_left h.2 hδ
    dsimp [w, s]
    split <;> linarith
  have hsum (t z) : ∑ c, w t z c = 1 := by simp [Fin.sum_univ_two, w, s]; ring
  let W (t : ZMod q) := ∑ x ∈ G, ∑ c, ∏ i, w t (x i) c
  let μ : ℝ := 2 * (1 / 2) ^ k - 4 * δ ^ k
  have moment (x) (hx : x ∈ G) : ∑ t : ZMod q, ∑ c, ∏ i, w t (x i) c = q * μ := by
    rw [sum_comm]
    have eqn (c : Fin 2) := wave_moment a x ha u hu hp (s c) (hmod x hx)
    simp only [w, eqn, Fin.sum_univ_two]
    simp [s, hk.neg_pow, μ]
    ring
  have total : ∑ t : ZMod q, W t = ∑ _t : ZMod q, G.card * μ := by
    simp only [W]
    rw [sum_comm, sum_congr rfl moment]
    simp [nsmul_eq_mul, mul_left_comm]
  obtain ⟨t, -, ht⟩ := exists_le_of_sum_le univ_nonempty total.le
  obtain ⟨χ, hχ⟩ := round_good n G (fun x hx i =>
    mem_Icc.mpr ((mem_solutions.mp (mem_sdiff.mp hx).1).1 i)) (fun x hx => by
      by_contra hi
      exact (mem_sdiff.mp hx).2 (mem_union_left _ (mem_filter.mpr ⟨(mem_sdiff.mp hx).1, hi⟩)))
    (w t) (hw t) (hsum t)
  exact ⟨χ, hχ.trans ht⟩

-- The expected saving absorbs both the exceptional tuples and the rounding error from repeats.
private lemma two_colours {k : ℕ} (hk : 3 ≤ k) (hev : Even k) (a : Fin k → ℤ)
    (ha : ∀ i, a i ≠ 0) (hs : ∃ i j, a i < 0 ∧ 0 < a j) (h : ¬ HasCancelingPartition a) :
    IsUncommonOverIntegers a 2 := by
  classical
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  obtain ⟨u, hun, hu, hp⟩ := phases a ha h
  let δ : ℝ := 1 / (2 * ((freq a).card + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : δ * (freq a).card ≤ 1 / 2 := by
    dsimp [δ]
    field_simp
    linarith
  obtain ⟨q, hq⟩ := exists_nat_ge ((δ ^ k)⁻¹)
  let Q := max 2 q
  have hQ : 1 ≤ (Q : ℝ) * δ ^ k := by
    have hle : (δ ^ k)⁻¹ ≤ (Q : ℝ) := hq.trans (by exact_mod_cast le_max_right 2 q)
    simpa only [one_div] using (div_le_iff₀ (pow_pos hδ k)).mp (by simpa using hle)
  let R : ℝ := 2 ^ (k - 1)
  have hR : 0 < R := by dsimp [R]; positivity
  have baseline : R * (2 * (1 / 2 : ℝ) ^ k) = 1 := by
    have he : k - 1 + 1 = k := by omega
    dsimp [R]
    rw [← mul_assoc, ← pow_succ, he, one_div, inv_pow, mul_inv_cancel₀ (by positivity)]
  apply (uncommon_iff a).mpr
  refine ⟨R * δ ^ k / 2, by positivity, frequently_atTop.mpr fun n₀ => ?_⟩
  obtain ⟨n, hn, hpos, hbad⟩ := large_interval hk a ha hs Q n₀
  let S := solutions a n
  let B := bad a n
  let G := S \ B
  obtain ⟨χ, hχ⟩ := colour_good hev a ha u hun hu hp δ hδ.le hsmall n
  refine ⟨n, hn, χ, ?_⟩
  have hbs : (Q : ℝ) * B.card ≤ S.card := by exact_mod_cast hbad
  have hBG : (S.card : ℝ) ≤ G.card + B.card := by exact_mod_cast card_le_card_sdiff_add_card
  have hGS : (G.card : ℝ) ≤ S.card := by exact_mod_cast card_le_card sdiff_subset
  have hQ₂ : (2 : ℝ) ≤ Q := by exact_mod_cast le_max_left 2 q
  have half : (S.card : ℝ) ≤ 2 * G.card := by
    linarith [mul_le_mul_of_nonneg_right hQ₂ (Nat.cast_nonneg (α := ℝ) B.card)]
  have small : (B.card : ℝ) ≤ S.card * δ ^ k := calc
    _ ≤ B.card * (Q * δ ^ k) := le_mul_of_one_le_right (by positivity) hQ
    _ = (Q * B.card) * δ ^ k := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbs (pow_nonneg hδ.le k)
  have cover : S.filter (mono χ) ⊆ G.filter (mono χ) ∪ B := by
    intro x hx
    by_cases hb : x ∈ B
    · exact mem_union_right _ hb
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨(mem_filter.mp hx).1, hb⟩,
        (mem_filter.mp hx).2⟩)
  have hm : ((S.filter (mono χ)).card : ℝ) ≤ (G.filter (mono χ)).card + B.card := by
    exact_mod_cast (card_le_card cover).trans (card_union_le ..)
  have hχ' : ((G.filter (mono χ)).card : ℝ) ≤ G.card * (2 * (1 / 2) ^ k - 4 * δ ^ k) := hχ
  have bound : ((S.filter (mono χ)).card : ℝ) ≤ S.card * (2 * (1 / 2) ^ k - δ ^ k) := by
    linarith only [hm, hχ', small, mul_le_mul_of_nonneg_right half (pow_nonneg hδ.le k),
      mul_le_mul_of_nonneg_right hGS (show 0 ≤ 2 * (1 / 2 : ℝ) ^ k by positivity)]
  have hS : 0 < (S.card : ℝ) := by exact_mod_cast hpos
  change R * ((S.filter (mono χ)).card : ℝ) < (1 - R * δ ^ k / 2) * S.card
  calc
    _ ≤ R * (S.card * (2 * (1 / 2) ^ k - δ ^ k)) := mul_le_mul_of_nonneg_left bound hR.le
    _ = (1 - R * δ ^ k) * S.card := by linear_combination S.card * baseline
    _ < _ := by gcongr; linarith [mul_pos hR (pow_pos hδ k)]

end isUncommonOverIntegers_of_not_hasCancelingPartition

open isUncommonOverIntegers_of_not_hasCancelingPartition in
/-- **Uncommonness of even-length equations without a canceling partition.** Let $m \ge 2$
and let $a_1, \dots, a_{2m}$ be nonzero integers, at least one negative and at least one
positive, such that the equation $a_1x_1 + \cdots + a_{2m}x_{2m} = 0$ has no canceling
partition. Then this equation is $r$-uncommon over the integers for every $r \ge 2$.

The sign condition excludes equations such as $x_1 + x_2 + x_3 + x_4 = 0$, which has no
canceling partition and no solutions in positive integers.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Corollary 2 (`integers-2025-A88-cor-2`). -/
public theorem isUncommonOverIntegers_of_not_hasCancelingPartition (m : ℕ)
    (hm : 2 ≤ m) (a : Fin (2 * m) → ℤ) (ha : ∀ i, a i ≠ 0)
    (hsign : ∃ i j, a i < 0 ∧ 0 < a j) (hcan : ¬ HasCancelingPartition a) (r : ℕ)
    (hr : 2 ≤ r) :
    IsUncommonOverIntegers a r := by
  have hk : 3 ≤ 2 * m := by omega
  have h₂ := two_colours hk (even_two_mul m) a ha hsign hcan
  rcases eq_or_lt_of_le hr with h | h
  · simpa [← h] using h₂
  · exact isUncommonOverIntegers_of_two _ hk a ha h₂ r (by omega)

end MetaMathlibExt
