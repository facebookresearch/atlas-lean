/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-! # Peak generating function for set partitions, Chebyshev form

This file proves the Mansour-Shattuck peak generating function for set partitions,
encoded as surjective restricted-growth strings.
-/

/-- **Surjective restricted-growth strings.** A word $w = w_0 w_1 \cdots w_{n-1}$ of length $n$
with letters in $\{0, 1, \dots, k-1\}$ is a surjective restricted-growth string if every letter
$0, \dots, k-1$ occurs in $w$ and, for every position $i$ and every letter $m < w_i$, some
position $j < i$ has $w_j = m$. -/
def IsSurjectiveRestrictedGrowthString {n k : ℕ} (w : Fin n → Fin k) : Prop :=
  Function.Surjective w ∧
    ∀ i : Fin n, ∀ m : Fin k,
      m.val < (w i).val → ∃ j : Fin n, j.val < i.val ∧ w j = m

/-- Decidability of the restricted-growth predicate (finite quantification). -/
instance (n k : ℕ) : DecidablePred (@IsSurjectiveRestrictedGrowthString n k) := by
  intro w
  unfold IsSurjectiveRestrictedGrowthString Function.Surjective
  infer_instance

private abbrev pgfR := PowerSeries (Polynomial ℤ)

private abbrev pgfK := FractionRing pgfR

private noncomputable def pgf_x : pgfR := PowerSeries.X

private noncomputable def pgf_q : pgfR := PowerSeries.C Polynomial.X

private noncomputable def pgf_y : pgfR := pgf_x ^ 2 * (1 - pgf_q)

private noncomputable def pgf_G : ℕ → pgfR
  | 0 => 1
  | 1 => 1
  | n + 2 => (2 + pgf_y) * pgf_G (n + 1) - pgf_G n

private lemma pgf_G_constantCoeff (n : ℕ) :
    PowerSeries.constantCoeff (pgf_G n) = 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [pgf_G]
  | one => simp [pgf_G]
  | more n hn hn1 =>
      rw [pgf_G]
      simp [pgf_y, pgf_x, hn, hn1, map_ofNat]
      ring

private lemma pgf_G_ne_zero (n : ℕ) : pgf_G n ≠ 0 := by
  intro h
  have hc := congrArg PowerSeries.constantCoeff h
  rw [pgf_G_constantCoeff, map_zero] at hc
  exact one_ne_zero hc

private noncomputable def pgf_map (f : pgfR) : pgfK :=
  algebraMap pgfR pgfK f

private noncomputable def pgf_t : pgfK :=
  1 + pgf_map pgf_x ^ 2 * (1 - pgf_map pgf_q) / 2

private noncomputable def pgf_U (m : ℤ) : pgfK :=
  (Polynomial.Chebyshev.U pgfK m).eval pgf_t

private lemma pgf_two_ne_zero : (2 : pgfK) ≠ 0 := by
  have hR : (2 : pgfR) ≠ 0 := by
    intro h
    have hc := congrArg PowerSeries.constantCoeff h
    rw [map_ofNat, map_zero] at hc
    norm_num at hc
  intro hK
  have hmap : algebraMap pgfR pgfK (2 : pgfR) = 0 := by
    rw [map_ofNat]
    exact hK
  apply hR
  apply IsFractionRing.injective pgfR pgfK
  simpa using hmap

private lemma pgf_two_mul_t : 2 * pgf_t = 2 + pgf_map pgf_y := by
  unfold pgf_t pgf_y pgf_map
  simp only [map_mul, map_pow, map_sub, map_one]
  field_simp [pgf_two_ne_zero]

private lemma pgf_U_add_two (n : ℤ) :
    pgf_U (n + 2) = 2 * pgf_t * pgf_U (n + 1) - pgf_U n := by
  unfold pgf_U
  rw [Polynomial.Chebyshev.U_add_two]
  simp

private lemma pgf_U_diff_recurrence (n : ℤ) :
    pgf_U (n + 1) - pgf_U n =
      (2 + pgf_map pgf_y) * (pgf_U n - pgf_U (n - 1)) -
        (pgf_U (n - 1) - pgf_U (n - 2)) := by
  have h1 : pgf_U (n + 1) = 2 * pgf_t * pgf_U n - pgf_U (n - 1) := by
    convert pgf_U_add_two (n - 1) using 1 <;> ring_nf
  have h0 : pgf_U n = 2 * pgf_t * pgf_U (n - 1) - pgf_U (n - 2) := by
    convert pgf_U_add_two (n - 2) using 1 <;> ring_nf
  rw [h1, h0, ← pgf_two_mul_t]
  ring

private lemma pgf_G_eq_U_diff (n : ℕ) :
    pgf_map (pgf_G n) = pgf_U ((n : ℤ) - 1) - pgf_U ((n : ℤ) - 2) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [pgf_G, pgf_map, pgf_U, Polynomial.Chebyshev.U_neg_one,
        Polynomial.Chebyshev.U_neg_two]
  | one =>
      simp [pgf_G, pgf_map, pgf_U, Polynomial.Chebyshev.U_zero,
        Polynomial.Chebyshev.U_neg_one]
  | more n hn hn1 =>
      rw [pgf_G]
      unfold pgf_map at hn hn1 ⊢
      rw [map_sub, map_mul, map_add, map_ofNat, hn, hn1]
      have hrec := pgf_U_diff_recurrence (n : ℤ)
      unfold pgf_map at hrec
      have e1 : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
      have e2 : ((n + 1 : ℕ) : ℤ) - 2 = (n : ℤ) - 1 := by omega
      have e3 : ((n + 2 : ℕ) : ℤ) - 1 = (n : ℤ) + 1 := by omega
      have e4 : ((n + 2 : ℕ) : ℤ) - 2 = (n : ℤ) := by omega
      rw [e1, e2, e3, e4]
      exact hrec.symm

private noncomputable def pgf_A : pgfR := pgf_x * (pgf_q - 1)

private noncomputable def pgf_B : pgfR := 1 - pgf_x * (pgf_q - 1)

private noncomputable def pgf_C : pgfR :=
  1 - pgf_x * (1 - pgf_q) * (1 - pgf_x)

private noncomputable def pgf_D : pgfR :=
  -pgf_x * (pgf_x + pgf_q * (1 - pgf_x))

private lemma pgf_A_add_B : pgf_A + pgf_B = 1 := by
  unfold pgf_A pgf_B
  ring

private lemma pgf_BC_sub_AD : pgf_B * pgf_C - pgf_A * pgf_D = 1 := by
  unfold pgf_A pgf_B pgf_C pgf_D
  ring

private lemma pgf_B_add_C : pgf_B + pgf_C = 2 + pgf_y := by
  unfold pgf_B pgf_C pgf_y
  ring

private def pgf_isPeakAt {n m : ℕ} (w : Fin n → Fin m) (i : Fin n) : Prop :=
  i.val ≠ 0 ∧
    if h : i.val + 1 < n then
      w ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩ < w i ∧
        w ⟨i.val + 1, h⟩ < w i
    else False

private instance {n m : ℕ} (w : Fin n → Fin m) : DecidablePred (pgf_isPeakAt w) := by
  intro i
  unfold pgf_isPeakAt
  infer_instance

private def pgf_peak {n m : ℕ} (w : Fin n → Fin m) : ℕ :=
  (Finset.univ.filter (pgf_isPeakAt w)).card

private def pgf_peakTriples {n m : ℕ} (w : Fin n → Fin m) : ℕ :=
  (Finset.univ.filter fun s : Fin n × Fin n × Fin n =>
    s.1.val + 1 = s.2.1.val ∧ s.2.1.val + 1 = s.2.2.val ∧
      w s.1 < w s.2.1 ∧ w s.2.2 < w s.2.1).card

private lemma pgf_peakTriples_eq_peak {n m : ℕ} (w : Fin n → Fin m) :
    pgf_peakTriples w = pgf_peak w := by
  unfold pgf_peakTriples pgf_peak
  apply Finset.card_bij (fun s _ => s.2.1)
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    rcases hs with ⟨h01, h12, hleft, hright⟩
    unfold pgf_isPeakAt
    have hnext : s.2.1.val + 1 < n := by omega
    refine ⟨by omega, ?_⟩
    rw [dite_eq_left hnext]
    have hprev :
        (⟨s.2.1.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) s.2.1.isLt⟩ : Fin n) = s.1 :=
      Fin.ext (by
        change s.2.1.val - 1 = s.1.val
        omega)
    have hsucc : (⟨s.2.1.val + 1, hnext⟩ : Fin n) = s.2.2 :=
      Fin.ext (by
        change s.2.1.val + 1 = s.2.2.val
        omega)
    simpa [hprev, hsucc] using And.intro hleft hright
  · intro s₁ hs₁ s₂ hs₂ hmid
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs₁ hs₂
    apply Prod.ext
    · exact Fin.ext (by omega)
    · apply Prod.ext
      · exact hmid
      · exact Fin.ext (by omega)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    unfold pgf_isPeakAt at hi
    rcases hi with ⟨hi0, hi⟩
    by_cases hnext : i.val + 1 < n
    · rw [dite_eq_left hnext] at hi
      let a : Fin n :=
        ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩
      let c : Fin n := ⟨i.val + 1, hnext⟩
      refine ⟨(a, i, c), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨by simp [a]; omega, by simp [c], ?_, ?_⟩
      · exact hi.1
      · exact hi.2
    · rw [dite_eq_right hnext] at hi
      exact False.elim hi

private noncomputable def pgf_W (m : ℕ) : pgfR :=
  PowerSeries.mk fun n => ∑ w : Fin n → Fin m, Polynomial.X ^ pgf_peak w

private noncomputable def pgf_PP (k : ℕ) : pgfR :=
  PowerSeries.mk fun n => ∑ w ∈ Finset.univ.filter
    (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
    Polynomial.X ^ pgf_peak w

private def pgf_peakNat {m K : ℕ} (w : Fin m → Fin K) (v : ℕ) : ℕ :=
  if h : v < m then
    if _ : 0 < v then
      if hv1 : v + 1 < m then
        if w ⟨v - 1, lt_of_le_of_lt (Nat.sub_le v 1) h⟩ < w ⟨v, h⟩ ∧
            w ⟨v + 1, hv1⟩ < w ⟨v, h⟩ then 1 else 0
      else 0
    else 0
  else 0

private lemma pgf_peak_eq_sum {m K : ℕ} (w : Fin m → Fin K) :
    pgf_peak w = ∑ v ∈ Finset.range m, pgf_peakNat w v := by
  have hcard : pgf_peak w = ∑ i : Fin m, (if pgf_isPeakAt w i then 1 else 0) := by
    change (Finset.univ.filter _).card = _
    rw [Finset.card_filter]
  rw [hcard, ← Fin.sum_univ_eq_sum_range (pgf_peakNat w) m]
  apply Finset.sum_congr rfl
  intro i _
  unfold pgf_isPeakAt pgf_peakNat
  split_ifs with h1 h2 h3 h4 h5
  all_goals simp_all

private abbrev pgfFirstData (n m : ℕ) :=
  Σ i : Fin n, (Fin i.val → Fin m) × (Fin (n - 1 - i.val) → Fin (m + 1))

private def pgf_joinFirst {n m : ℕ} (d : pgfFirstData n m) : Fin n → Fin (m + 1) :=
  fun j =>
    if hlt : j.val < d.1.val then d.2.1 ⟨j.val, hlt⟩ |>.castSucc
    else if heq : j.val = d.1.val then Fin.last m
    else d.2.2 ⟨j.val - d.1.val - 1, by omega⟩

private lemma pgf_joinFirst_top {n m : ℕ} (d : pgfFirstData n m) :
    pgf_joinFirst d d.1 = Fin.last m := by
  simp [pgf_joinFirst]

private lemma pgf_joinFirst_before {n m : ℕ} (i : Fin n) (u : Fin i.val → Fin m)
    (v : Fin (n - 1 - i.val) → Fin (m + 1)) (j : Fin i.val) :
    pgf_joinFirst ⟨i, u, v⟩ ⟨j.val, lt_trans j.isLt i.isLt⟩ = (u j).castSucc := by
  simp [pgf_joinFirst, j.isLt]

private lemma pgf_joinFirst_after {n m : ℕ} (i : Fin n) (u : Fin i.val → Fin m)
    (v : Fin (n - 1 - i.val) → Fin (m + 1)) (j : Fin (n - 1 - i.val)) :
    pgf_joinFirst ⟨i, u, v⟩ ⟨i.val + 1 + j.val, by omega⟩ = v j := by
  unfold pgf_joinFirst
  dsimp
  have hnlt : ¬i.val + 1 + j.val < i.val := by omega
  have hneq : i.val + 1 + j.val ≠ i.val := by omega
  rw [dite_eq_right hnlt, dite_eq_right hneq]
  congr 1
  apply Fin.ext
  change (i.val + 1 + j.val - i.val - 1) = j.val
  omega

private lemma pgf_joinFirst_top_le {n m : ℕ} (d : pgfFirstData n m) (j : Fin n)
    (h : pgf_joinFirst d j = Fin.last m) : d.1.val ≤ j.val := by
  by_contra hnle
  have hlt : j.val < d.1.val := by omega
  unfold pgf_joinFirst at h
  rw [dite_eq_left hlt] at h
  exact Fin.castSucc_ne_last _ h

private lemma pgf_joinFirst_injective (n m : ℕ) :
    Function.Injective (@pgf_joinFirst n m) := by
  rintro ⟨i, u, v⟩ ⟨i', u', v'⟩ h
  have hii' : i.val ≤ i'.val := by
    apply pgf_joinFirst_top_le ⟨i, u, v⟩ i'
    have hi' := congrFun h i'
    rw [pgf_joinFirst_top] at hi'
    exact hi'
  have hi'i : i'.val ≤ i.val := by
    apply pgf_joinFirst_top_le ⟨i', u', v'⟩ i
    have hi := congrFun h i
    rw [pgf_joinFirst_top] at hi
    exact hi.symm
  have heq : i = i' := Fin.ext (by omega)
  subst i'
  have hu : u = u' := by
    funext j
    apply Fin.castSucc_injective
    have hj := congrFun h ⟨j.val, lt_trans j.isLt i.isLt⟩
    simpa only [pgf_joinFirst_before] using hj
  have hv : v = v' := by
    funext j
    have hj := congrFun h ⟨i.val + 1 + j.val, by omega⟩
    simpa only [pgf_joinFirst_after] using hj
  subst u'
  subst v'
  rfl

private def pgf_decodeFirst (n m : ℕ) :
    (Fin n → Fin m) ⊕ pgfFirstData n m → Fin n → Fin (m + 1)
  | Sum.inl u => Fin.castSucc ∘ u
  | Sum.inr d => pgf_joinFirst d

private lemma pgf_decodeFirst_injective (n m : ℕ) :
    Function.Injective (pgf_decodeFirst n m) := by
  rintro (u | d) (u' | d') h
  · congr 1
    funext j
    apply Fin.castSucc_injective
    exact congrFun h j
  · have hi := congrFun h d'.1
    simp only [pgf_decodeFirst, Function.comp_apply, pgf_joinFirst_top] at hi
    exact False.elim (Fin.castSucc_ne_last _ hi)
  · have hi := congrFun h d.1
    simp only [pgf_decodeFirst, Function.comp_apply, pgf_joinFirst_top] at hi
    exact False.elim (Fin.castSucc_ne_last _ hi.symm)
  · congr 1
    exact pgf_joinFirst_injective n m h

private lemma pgf_decodeFirst_surjective (n m : ℕ) :
    Function.Surjective (pgf_decodeFirst n m) := by
  intro w
  by_cases htop : ∃ i, w i = Fin.last m
  · have hex : ∃ r : ℕ, ∃ hr : r < n, w ⟨r, hr⟩ = Fin.last m := by
      obtain ⟨i, hi⟩ := htop
      exact ⟨i.val, i.isLt, hi⟩
    let p := Nat.find hex
    have hpspec : ∃ hp : p < n, w ⟨p, hp⟩ = Fin.last m := by
      simpa [p] using Nat.find_spec hex
    obtain ⟨hp, hptop⟩ := hpspec
    have hbefore : ∀ r < p, ∀ hr : r < n, w ⟨r, hr⟩ ≠ Fin.last m := by
      intro r hr hrn heq
      exact (Nat.find_min hex (by simpa [p] using hr)) ⟨hrn, heq⟩
    let i : Fin n := ⟨p, hp⟩
    let u : Fin p → Fin m := fun j =>
      (w ⟨j.val, lt_trans j.isLt hp⟩).castPred (hbefore j.val j.isLt _)
    let v : Fin (n - 1 - p) → Fin (m + 1) := fun j =>
      w ⟨p + 1 + j.val, by omega⟩
    refine ⟨Sum.inr ⟨i, u, v⟩, ?_⟩
    funext j
    change pgf_joinFirst ⟨i, u, v⟩ j = w j
    unfold pgf_joinFirst
    dsimp only [i]
    by_cases hjp : j.val < p
    · rw [dite_eq_left hjp]
      dsimp only [u]
      rw [Fin.castSucc_castPred]
    · rw [dite_eq_right hjp]
      by_cases hjpeq : j.val = p
      · rw [dite_eq_left hjpeq]
        have hji : j = ⟨p, hp⟩ := Fin.ext hjpeq
        rw [hji, hptop]
      · rw [dite_eq_right hjpeq]
        dsimp only [v]
        congr 1
        apply Fin.ext
        dsimp
        omega
  · let u : Fin n → Fin m := fun i => (w i).castPred (fun hi => htop ⟨i, hi⟩)
    refine ⟨Sum.inl u, ?_⟩
    funext i
    change (u i).castSucc = w i
    exact Fin.castSucc_castPred _ _

private noncomputable def pgf_firstTopEquiv (n m : ℕ) :
    ((Fin n → Fin m) ⊕ pgfFirstData n m) ≃ (Fin n → Fin (m + 1)) :=
  Equiv.ofBijective (pgf_decodeFirst n m)
    ⟨pgf_decodeFirst_injective n m, pgf_decodeFirst_surjective n m⟩

@[simp] private lemma pgf_last_not_lt_castSucc {m : ℕ} (a : Fin m) :
    ¬Fin.last m < a.castSucc :=
  fun h => (Fin.castSucc_lt_last a).asymm h

@[simp] private lemma pgf_last_not_lt {m : ℕ} (a : Fin (m + 1)) :
    ¬Fin.last m < a :=
  not_lt_of_ge (Fin.le_last a)

private lemma pgf_peakNat_join_before {n m : ℕ} (i : Fin n) (u : Fin i.val → Fin m)
    (v : Fin (n - 1 - i.val) → Fin (m + 1)) (j : ℕ) (hj : j < i.val) :
    pgf_peakNat (pgf_joinFirst ⟨i, u, v⟩) j = pgf_peakNat u j := by
  unfold pgf_peakNat pgf_joinFirst
  dsimp
  split_ifs <;> simp_all <;> omega

@[simp] private lemma pgf_suffix_index {n : ℕ} (i : Fin n) (j : ℕ)
    (hj : j < n - 1 - i.val) (h : i.val + 1 + j - i.val - 1 < n - 1 - i.val) :
    (⟨i.val + 1 + j - i.val - 1, h⟩ : Fin (n - 1 - i.val)) = ⟨j, hj⟩ := by
  apply Fin.ext
  change i.val + 1 + j - i.val - 1 = j
  omega

@[simp] private lemma pgf_suffix_prev_index {n : ℕ} (i : Fin n) (j : ℕ)
    (hj : j < n - 1 - i.val) (hj0 : 0 < j)
    (h : i.val + 1 + j - 1 - i.val - 1 < n - 1 - i.val) :
    (⟨i.val + 1 + j - 1 - i.val - 1, h⟩ : Fin (n - 1 - i.val)) =
      ⟨j - 1, by omega⟩ := by
  apply Fin.ext
  change i.val + 1 + j - 1 - i.val - 1 = j - 1
  omega

@[simp] private lemma pgf_suffix_next_index {n : ℕ} (i : Fin n) (j : ℕ)
    (hj1 : j + 1 < n - 1 - i.val)
    (h : i.val + 1 + j + 1 - i.val - 1 < n - 1 - i.val) :
    (⟨i.val + 1 + j + 1 - i.val - 1, h⟩ : Fin (n - 1 - i.val)) =
      ⟨j + 1, hj1⟩ := by
  apply Fin.ext
  change i.val + 1 + j + 1 - i.val - 1 = j + 1
  omega

set_option maxHeartbeats 1000000 in
-- Expanding the dependent peak and splice conditionals produces many arithmetic branches.
private lemma pgf_peakNat_join_after {n m : ℕ} (i : Fin n) (u : Fin i.val → Fin m)
    (v : Fin (n - 1 - i.val) → Fin (m + 1)) (j : ℕ)
    (hj : j < n - 1 - i.val) :
    pgf_peakNat (pgf_joinFirst ⟨i, u, v⟩) (i.val + 1 + j) = pgf_peakNat v j := by
  unfold pgf_peakNat pgf_joinFirst
  dsimp
  split_ifs <;> simp_all <;> omega

private def pgf_boundary {n m : ℕ} (d : pgfFirstData n m) : ℕ :=
  if _ : 0 < d.1.val then
    if hv : 0 < n - 1 - d.1.val then
      if d.2.2 ⟨0, hv⟩ < Fin.last m then 1 else 0
    else 0
  else 0

private lemma pgf_peakNat_join_top {n m : ℕ} (i : Fin n) (u : Fin i.val → Fin m)
    (v : Fin (n - 1 - i.val) → Fin (m + 1)) :
    pgf_peakNat (pgf_joinFirst ⟨i, u, v⟩) i.val = pgf_boundary ⟨i, u, v⟩ := by
  unfold pgf_peakNat pgf_boundary pgf_joinFirst
  dsimp
  split_ifs <;> try simp_all [Fin.castSucc_lt_last] <;> try omega

private lemma pgf_peak_join {n m : ℕ} (i : Fin n) (u : Fin i.val → Fin m)
    (v : Fin (n - 1 - i.val) → Fin (m + 1)) :
    pgf_peak (pgf_joinFirst ⟨i, u, v⟩) =
      pgf_peak u + pgf_boundary ⟨i, u, v⟩ + pgf_peak v := by
  rw [pgf_peak_eq_sum, pgf_peak_eq_sum, pgf_peak_eq_sum]
  rw [show Finset.range n = Finset.range (i.val + (1 + (n - 1 - i.val))) by
    congr 1
    omega]
  rw [Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [Finset.sum_range_add]
  have hprefix :
      (∑ j ∈ Finset.range i.val, pgf_peakNat (pgf_joinFirst ⟨i, u, v⟩) j) =
        ∑ j ∈ Finset.range i.val, pgf_peakNat u j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact pgf_peakNat_join_before i u v j (Finset.mem_range.mp hj)
  have hsuffix :
      (∑ j ∈ Finset.range (n - 1 - i.val),
          pgf_peakNat (pgf_joinFirst ⟨i, u, v⟩) (i.val + (1 + j))) =
        ∑ j ∈ Finset.range (n - 1 - i.val), pgf_peakNat v j := by
    apply Finset.sum_congr rfl
    intro j hj
    simpa [Nat.add_assoc] using
      pgf_peakNat_join_after i u v j (Finset.mem_range.mp hj)
  rw [hprefix, hsuffix]
  simp only [Finset.sum_range_one, add_zero, pgf_peakNat_join_top]
  omega

private lemma pgf_peakNat_cons_last {n m : ℕ} (v : Fin n → Fin (m + 1)) (j : ℕ)
    (hj : j < n) :
    pgf_peakNat (Fin.cons (Fin.last m) v) (j + 1) = pgf_peakNat v j := by
  have hlast (a : Fin (m + 1)) : ¬Fin.last m < a := not_lt_of_ge (Fin.le_last a)
  by_cases hj0 : j = 0
  · subst j
    unfold pgf_peakNat
    simp [Fin.cons, hlast]
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  have hcur (h : j + 1 < n + 1) :
      @Fin.cons n (fun _ => Fin (m + 1)) (Fin.last m) v ⟨j + 1, h⟩ = v ⟨j, hj⟩ := by
    rw [show (⟨j + 1, h⟩ : Fin (n + 1)) = Fin.succ ⟨j, hj⟩ by
      apply Fin.ext
      rfl]
    exact Fin.cons_succ _ _ _
  have hprev (hj0 : 0 < j) (h : j + 1 - 1 < n + 1) :
      @Fin.cons n (fun _ => Fin (m + 1)) (Fin.last m) v ⟨j + 1 - 1, h⟩ =
        v ⟨j - 1, by omega⟩ := by
    rw [show (⟨j + 1 - 1, h⟩ : Fin (n + 1)) = Fin.succ ⟨j - 1, by omega⟩ by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega]
    exact Fin.cons_succ _ _ _
  have hnext (hj1 : j + 1 < n) (h : j + 1 + 1 < n + 1) :
      @Fin.cons n (fun _ => Fin (m + 1)) (Fin.last m) v ⟨j + 1 + 1, h⟩ =
        v ⟨j + 1, hj1⟩ := by
    rw [show (⟨j + 1 + 1, h⟩ : Fin (n + 1)) = Fin.succ ⟨j + 1, hj1⟩ by
      apply Fin.ext
      rfl]
    exact Fin.cons_succ _ _ _
  unfold pgf_peakNat
  split_ifs <;> simp_all <;> try omega
  all_goals
    have hp := hprev (by omega)
    simp_all
    omega

private lemma pgf_peak_cons_last {n m : ℕ} (v : Fin n → Fin (m + 1)) :
    pgf_peak (Fin.cons (Fin.last m) v) = pgf_peak v := by
  rw [pgf_peak_eq_sum, pgf_peak_eq_sum, Finset.sum_range_succ']
  have hzero : pgf_peakNat (Fin.cons (Fin.last m) v) 0 = 0 := by
    unfold pgf_peakNat
    simp
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact pgf_peakNat_cons_last v j (Finset.mem_range.mp hj)

private lemma pgf_sum_start_last (n m : ℕ) :
    (∑ w ∈ Finset.univ.filter (fun w : Fin (n + 1) → Fin (m + 1) =>
        ¬w 0 < Fin.last m), (Polynomial.X : Polynomial ℤ) ^ pgf_peak w) =
      ∑ v : Fin n → Fin (m + 1), (Polynomial.X : Polynomial ℤ) ^ pgf_peak v := by
  symm
  apply Finset.sum_bij (s := Finset.univ)
    (t := Finset.univ.filter (fun w : Fin (n + 1) → Fin (m + 1) =>
      ¬w 0 < Fin.last m)) (fun v _ => Fin.cons (Fin.last m) v)
  · intro v _
    simp
  · intro v₁ _ v₂ _ h
    funext j
    have hj := congrFun h j.succ
    simpa only [Fin.cons_succ] using hj
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    have hw0 : w 0 = Fin.last m :=
      le_antisymm (Fin.le_last _) (le_of_not_gt hw)
    refine ⟨Fin.tail w, Finset.mem_univ _, ?_⟩
    calc
      Fin.cons (Fin.last m) (Fin.tail w) = Fin.cons (w 0) (Fin.tail w) := by rw [hw0]
      _ = w := Fin.cons_self_tail w
  · intro v _
    simp only [pgf_peak_cons_last]

private noncomputable def pgf_L (m : ℕ) : pgfR :=
  PowerSeries.mk fun n =>
    if h : 0 < n then
      ∑ w ∈ Finset.univ.filter (fun w : Fin n → Fin (m + 1) =>
        w ⟨0, h⟩ < Fin.last m), (Polynomial.X : Polynomial ℤ) ^ pgf_peak w
    else 0

private lemma pgf_L_eq (m : ℕ) :
    pgf_L m = pgf_W (m + 1) - 1 - pgf_x * pgf_W (m + 1) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp [pgf_L, pgf_W, pgf_x, pgf_peak]
  | succ n =>
      simp only [pgf_L, PowerSeries.coeff_mk, Nat.zero_lt_succ, dite_true,
        map_sub, PowerSeries.coeff_one, Nat.succ_ne_zero, ite_false, sub_zero,
        pgf_x, PowerSeries.coeff_succ_X_mul, pgf_W]
      have hsplit := Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ) (p := fun w : Fin (n + 1) → Fin (m + 1) =>
          w 0 < Fin.last m)
        (f := fun w => (Polynomial.X : Polynomial ℤ) ^ pgf_peak w)
      rw [pgf_sum_start_last n m] at hsplit
      rw [← hsplit]
      ring_nf
      congr 2

private noncomputable def pgf_H (m : ℕ) : pgfR :=
  PowerSeries.mk fun n =>
    ∑ d : pgfFirstData n m, (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst d)

private lemma pgf_W_succ_eq (m : ℕ) : pgf_W (m + 1) = pgf_W m + pgf_H m := by
  apply PowerSeries.ext
  intro n
  simp only [pgf_W, pgf_H, map_add, PowerSeries.coeff_mk]
  rw [← Equiv.sum_comp (pgf_firstTopEquiv n m)
    (fun w => (Polynomial.X : Polynomial ℤ) ^ pgf_peak w)]
  rw [Fintype.sum_sum_type]
  congr 1

private lemma pgf_join_weight {n m : ℕ} (i : Fin n) (u : Fin i.val → Fin m)
    (v : Fin (n - 1 - i.val) → Fin (m + 1)) :
    (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst ⟨i, u, v⟩) =
      Polynomial.X ^ pgf_peak u * Polynomial.X ^ pgf_peak v +
        (Polynomial.X - 1) *
          (if pgf_boundary ⟨i, u, v⟩ = 1 then
            Polynomial.X ^ pgf_peak u * Polynomial.X ^ pgf_peak v else 0) := by
  rw [pgf_peak_join, pow_add, pow_add]
  by_cases hi : 0 < i.val
  · by_cases hv : 0 < n - 1 - i.val
    · by_cases hb : v ⟨0, hv⟩ < Fin.last m
      · simp [pgf_boundary, hi, hv, hb]
        ring
      · simp [pgf_boundary, hi, hv, hb]
    · simp [pgf_boundary, hi, hv]
  · simp [pgf_boundary, hi]

private lemma pgf_join_weight_data {n m : ℕ} (d : pgfFirstData n m) :
    (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst d) =
      Polynomial.X ^ pgf_peak d.2.1 * Polynomial.X ^ pgf_peak d.2.2 +
        (Polynomial.X - 1) *
          (if pgf_boundary d = 1 then
            Polynomial.X ^ pgf_peak d.2.1 * Polynomial.X ^ pgf_peak d.2.2 else 0) := by
  rcases d with ⟨i, u, v⟩
  exact pgf_join_weight i u v

private lemma pgf_base_sum (n m : ℕ) :
    (∑ i : Fin (n + 1), ∑ uv :
        (Fin i.val → Fin m) × (Fin (n + 1 - 1 - i.val) → Fin (m + 1)),
      (Polynomial.X : Polynomial ℤ) ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2) =
      ∑ k ∈ Finset.range (n + 1),
        PowerSeries.coeff k (pgf_W m) * PowerSeries.coeff (n - k) (pgf_W (m + 1)) := by
  apply Finset.sum_bij (s := Finset.univ) (t := Finset.range (n + 1))
    (fun i _ => i.val)
  · intro i _
    exact Finset.mem_range.mpr i.isLt
  · intro i₁ _ i₂ _ h
    exact Fin.ext h
  · intro k hk
    refine ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
  · intro i _
    simp only [pgf_W, PowerSeries.coeff_mk]
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    rfl

private lemma pgf_coeff_W_sub_one (n m : ℕ) :
    PowerSeries.coeff n (pgf_W m - 1) =
      if 0 < n then
        ∑ u : Fin n → Fin m, (Polynomial.X : Polynomial ℤ) ^ pgf_peak u
      else 0 := by
  cases n with
  | zero => simp [pgf_W, pgf_peak]
  | succ n => simp [pgf_W]

private lemma pgf_boundary_sum_coeff (n m : ℕ) (i : Fin (n + 1)) :
    (∑ uv : (Fin i.val → Fin m) ×
        (Fin (n + 1 - 1 - i.val) → Fin (m + 1)),
      if pgf_boundary ⟨i, uv⟩ = 1 then
        (Polynomial.X : Polynomial ℤ) ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
      else 0) =
      PowerSeries.coeff i.val (pgf_W m - 1) *
        PowerSeries.coeff (n - i.val) (pgf_L m) := by
  rw [pgf_coeff_W_sub_one]
  simp only [pgf_L, PowerSeries.coeff_mk]
  rw [Fintype.sum_prod_type]
  by_cases hi : 0 < i.val
  · by_cases hv : 0 < n - i.val
    · simp only [ite_eq_left hi, dite_eq_left hv]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hb : v ⟨0, hv⟩ < Fin.last m
      · simp [pgf_boundary, hi, hv, hb]
      · simp [pgf_boundary, hi, hv, hb]
    · simp only [ite_eq_left hi, dite_eq_right hv, mul_zero]
      apply Finset.sum_eq_zero
      intro u _
      apply Finset.sum_eq_zero
      intro v _
      simp [pgf_boundary, hi, hv]
  · simp only [ite_eq_right hi, zero_mul]
    apply Finset.sum_eq_zero
    intro u _
    apply Finset.sum_eq_zero
    intro v _
    simp [pgf_boundary, hi]

private lemma pgf_boundary_sum (n m : ℕ) :
    (∑ i : Fin (n + 1), ∑ uv :
        (Fin i.val → Fin m) × (Fin (n + 1 - 1 - i.val) → Fin (m + 1)),
      if pgf_boundary ⟨i, uv⟩ = 1 then
        (Polynomial.X : Polynomial ℤ) ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
      else 0) =
      ∑ k ∈ Finset.range (n + 1),
        PowerSeries.coeff k (pgf_W m - 1) * PowerSeries.coeff (n - k) (pgf_L m) := by
  apply Finset.sum_bij (s := Finset.univ) (t := Finset.range (n + 1))
    (fun i _ => i.val)
  · intro i _
    exact Finset.mem_range.mpr i.isLt
  · intro i₁ _ i₂ _ h
    exact Fin.ext h
  · intro k hk
    refine ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
  · intro i _
    exact pgf_boundary_sum_coeff n m i

private lemma pgf_H_eq (m : ℕ) :
    pgf_H m = pgf_x * (pgf_W m * pgf_W (m + 1) +
      (pgf_q - 1) * ((pgf_W m - 1) * pgf_L m)) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp [pgf_H, pgf_x]
  | succ n =>
      simp only [pgf_H, PowerSeries.coeff_mk, pgf_x,
        PowerSeries.coeff_succ_X_mul, map_add]
      rw [show pgf_q - 1 = PowerSeries.C ((Polynomial.X : Polynomial ℤ) - 1) by
        simp [pgf_q]]
      rw [PowerSeries.coeff_C_mul]
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      rw [Fintype.sum_sigma]
      calc
        (∑ i : Fin (n + 1), ∑ uv :
            (Fin i.val → Fin m) × (Fin (n + 1 - 1 - i.val) → Fin (m + 1)),
          (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst ⟨i, uv⟩)) =
            (∑ i : Fin (n + 1), ∑ uv :
              (Fin i.val → Fin m) × (Fin (n + 1 - 1 - i.val) → Fin (m + 1)),
              Polynomial.X ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2) +
            (Polynomial.X - 1) *
              (∑ i : Fin (n + 1), ∑ uv :
                (Fin i.val → Fin m) × (Fin (n + 1 - 1 - i.val) → Fin (m + 1)),
                if pgf_boundary ⟨i, uv⟩ = 1 then
                  Polynomial.X ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
                else 0) := by
          simp_rw [pgf_join_weight_data, Finset.sum_add_distrib, Finset.mul_sum]
        _ = _ := by rw [pgf_base_sum, pgf_boundary_sum]

private lemma pgf_W_raw_recurrence (m : ℕ) :
    pgf_W (m + 1) = pgf_W m +
      pgf_x * pgf_W m * pgf_W (m + 1) +
      pgf_x * (pgf_q - 1) * (pgf_W m - 1) *
        (pgf_W (m + 1) - 1 - pgf_x * pgf_W (m + 1)) := by
  calc
    pgf_W (m + 1) = pgf_W m + pgf_H m := pgf_W_succ_eq m
    _ = _ := by rw [pgf_H_eq, pgf_L_eq]; ring

private lemma pgf_W_recurrence (m : ℕ) :
    (pgf_C + pgf_D * pgf_W m) * pgf_W (m + 1) =
      pgf_A + pgf_B * pgf_W m := by
  have h := pgf_W_raw_recurrence m
  unfold pgf_A pgf_B pgf_C pgf_D at ⊢
  linear_combination h

private lemma pgf_W_zero : pgf_W 0 = 1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [pgf_W, pgf_peak]
  | succ n => simp [pgf_W]

private lemma pgf_G_recurrence (m : ℕ) :
    pgf_G (m + 2) = (pgf_B + pgf_C) * pgf_G (m + 1) - pgf_G m := by
  rw [pgf_G, pgf_B_add_C]

private lemma pgf_DA_sub_CB : pgf_D * pgf_A - pgf_C * pgf_B = -1 := by
  have h := pgf_BC_sub_AD
  linear_combination -h

private noncomputable def pgf_den (m : ℕ) : pgfR :=
  pgf_G (m + 1) - pgf_B * pgf_G m

private lemma pgf_W_G_identity (m : ℕ) :
    pgf_W m * pgf_den m = pgf_A * pgf_G m := by
  induction m with
  | zero =>
      rw [pgf_W_zero]
      simp only [pgf_den, pgf_G, one_mul, mul_one]
      rw [← pgf_A_add_B]
      ring
  | succ m ih =>
      have hden : (pgf_C + pgf_D * pgf_W m) * pgf_den m = pgf_den (m + 1) := by
        calc
          (pgf_C + pgf_D * pgf_W m) * pgf_den m =
              pgf_C * pgf_den m + pgf_D * (pgf_W m * pgf_den m) := by ring
          _ = pgf_C * pgf_den m + pgf_D * (pgf_A * pgf_G m) := by rw [ih]
          _ =
              pgf_C * pgf_G (m + 1) +
                (pgf_D * pgf_A - pgf_C * pgf_B) * pgf_G m := by
            rw [pgf_den]
            ring
          _ = pgf_C * pgf_G (m + 1) - pgf_G m := by rw [pgf_DA_sub_CB]; ring
          _ = pgf_den (m + 1) := by
            rw [pgf_den, pgf_G_recurrence]
            ring
      have hnum : (pgf_A + pgf_B * pgf_W m) * pgf_den m =
          pgf_A * pgf_G (m + 1) := by
        rw [add_mul, mul_assoc, ih, pgf_den]
        ring
      calc
        pgf_W (m + 1) * pgf_den (m + 1) =
            pgf_W (m + 1) * ((pgf_C + pgf_D * pgf_W m) * pgf_den m) := by
          rw [hden]
        _ = ((pgf_C + pgf_D * pgf_W m) * pgf_W (m + 1)) * pgf_den m := by ring
        _ = (pgf_A + pgf_B * pgf_W m) * pgf_den m := by rw [pgf_W_recurrence]
        _ = pgf_A * pgf_G (m + 1) := hnum

private lemma pgf_A_ne_zero : pgf_A ≠ 0 := by
  have hcoeff : PowerSeries.coeff 1 pgf_A = (Polynomial.X : Polynomial ℤ) - 1 := by
    unfold pgf_A pgf_x
    rw [show 1 = 0 + 1 by omega, PowerSeries.coeff_succ_X_mul]
    simp [pgf_q]
  intro h
  have hc := congrArg (PowerSeries.coeff 1) h
  rw [hcoeff, map_zero] at hc
  have hp := congrArg (fun p : Polynomial ℤ => p.coeff 1) hc
  norm_num [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_one] at hp

private lemma pgf_den_ne_zero (m : ℕ) : pgf_den m ≠ 0 := by
  intro hden
  have h := pgf_W_G_identity m
  rw [hden, mul_zero] at h
  exact (mul_ne_zero pgf_A_ne_zero (pgf_G_ne_zero m)) h.symm

private lemma pgf_map_G_ne_zero (m : ℕ) : pgf_map (pgf_G m) ≠ 0 := by
  intro h
  apply pgf_G_ne_zero m
  apply IsFractionRing.injective pgfR pgfK
  simpa [pgf_map] using h

private lemma pgf_map_den_ne_zero (m : ℕ) : pgf_map (pgf_den m) ≠ 0 := by
  intro h
  apply pgf_den_ne_zero m
  apply IsFractionRing.injective pgfR pgfK
  simpa [pgf_map] using h

private lemma pgf_W_ratio (m : ℕ) :
    pgf_map (pgf_W m) =
      pgf_map pgf_A /
        (pgf_map (pgf_G (m + 1)) / pgf_map (pgf_G m) - pgf_map pgf_B) := by
  have h := congrArg pgf_map (pgf_W_G_identity m)
  unfold pgf_map at h ⊢
  simp only [map_mul] at h
  unfold pgf_den at h
  simp only [map_sub, map_mul] at h
  have hg := pgf_map_G_ne_zero m
  unfold pgf_map at hg
  have hd : algebraMap pgfR pgfK (pgf_G (m + 1)) -
      algebraMap pgfR pgfK pgf_B * algebraMap pgfR pgfK (pgf_G m) ≠ 0 := by
    simpa [pgf_map, pgf_den] using pgf_map_den_ne_zero m
  have hr : algebraMap pgfR pgfK (pgf_G (m + 1)) /
      algebraMap pgfR pgfK (pgf_G m) - algebraMap pgfR pgfK pgf_B ≠ 0 := by
    intro hr
    apply hd
    calc
      algebraMap pgfR pgfK (pgf_G (m + 1)) -
          algebraMap pgfR pgfK pgf_B * algebraMap pgfR pgfK (pgf_G m) =
          (algebraMap pgfR pgfK (pgf_G (m + 1)) /
            algebraMap pgfR pgfK (pgf_G m) - algebraMap pgfR pgfK pgf_B) *
              algebraMap pgfR pgfK (pgf_G m) := by field_simp
      _ = 0 := by rw [hr, zero_mul]
  apply (eq_div_iff hr).2
  field_simp
  simpa [mul_comm] using h

private lemma pgf_rg_join_iff {n k : ℕ} (i : Fin n) (u : Fin i.val → Fin k)
    (v : Fin (n - 1 - i.val) → Fin (k + 1)) :
    IsSurjectiveRestrictedGrowthString (pgf_joinFirst ⟨i, u, v⟩) ↔
      IsSurjectiveRestrictedGrowthString u := by
  constructor
  · rintro ⟨_, hgrowth⟩
    constructor
    · intro a
      have halt : a.castSucc < Fin.last k := Fin.castSucc_lt_last a
      obtain ⟨j, hji, hj⟩ := hgrowth i a.castSucc (by
        rw [pgf_joinFirst_top]
        exact halt)
      let j' : Fin i.val := ⟨j.val, hji⟩
      refine ⟨j', ?_⟩
      apply Fin.castSucc_injective
      calc
        (u j').castSucc = pgf_joinFirst ⟨i, u, v⟩
            ⟨j'.val, lt_trans j'.isLt i.isLt⟩ := (pgf_joinFirst_before i u v j').symm
        _ = pgf_joinFirst ⟨i, u, v⟩ j := by
          congr 1
        _ = a.castSucc := hj
    · intro j a ha
      let jg : Fin n := ⟨j.val, lt_trans j.isLt i.isLt⟩
      have hjg : pgf_joinFirst ⟨i, u, v⟩ jg = (u j).castSucc := by
        exact pgf_joinFirst_before i u v j
      obtain ⟨l, hlj, hl⟩ := hgrowth jg a.castSucc (by
        rw [hjg]
        exact Fin.castSucc_lt_castSucc_iff.mpr ha)
      let l' : Fin i.val := ⟨l.val, lt_trans hlj j.isLt⟩
      refine ⟨l', hlj, ?_⟩
      apply Fin.castSucc_injective
      calc
        (u l').castSucc = pgf_joinFirst ⟨i, u, v⟩
            ⟨l'.val, lt_trans l'.isLt i.isLt⟩ := (pgf_joinFirst_before i u v l').symm
        _ = pgf_joinFirst ⟨i, u, v⟩ l := by
          congr 1
        _ = a.castSucc := hl
  · rintro ⟨hsurj, hgrowth⟩
    constructor
    · intro a
      by_cases ha : a = Fin.last k
      · exact ⟨i, by simpa [ha] using pgf_joinFirst_top ⟨i, u, v⟩⟩
      · obtain ⟨j, hj⟩ := hsurj (a.castPred ha)
        refine ⟨⟨j.val, lt_trans j.isLt i.isLt⟩, ?_⟩
        rw [show (⟨j.val, lt_trans j.isLt i.isLt⟩ : Fin n) =
            ⟨j.val, lt_trans j.isLt i.isLt⟩ by rfl,
          pgf_joinFirst_before]
        rw [hj, Fin.castSucc_castPred]
    · intro j a ha
      by_cases hji : j.val < i.val
      · let j' : Fin i.val := ⟨j.val, hji⟩
        have hj : pgf_joinFirst ⟨i, u, v⟩ j = (u j').castSucc := by
          calc
            pgf_joinFirst ⟨i, u, v⟩ j = pgf_joinFirst ⟨i, u, v⟩
                ⟨j'.val, lt_trans j'.isLt i.isLt⟩ := by
              congr 1
            _ = (u j').castSucc := pgf_joinFirst_before i u v j'
        have hane : a ≠ Fin.last k := by
          intro hatop
          rw [hatop, hj] at ha
          exact (Fin.castSucc_lt_last (u j')).asymm ha
        let a' : Fin k := a.castPred hane
        have haj : a' < u j' := by
          apply Fin.castSucc_lt_castSucc_iff.mp
          simpa only [a', Fin.castSucc_castPred] using (hj ▸ ha)
        obtain ⟨l, hlj, hl⟩ := hgrowth j' a' haj
        refine ⟨⟨l.val, lt_trans (lt_trans hlj j'.isLt) i.isLt⟩, ?_, ?_⟩
        · exact hlj
        · rw [pgf_joinFirst_before]
          simp only [hl, a', Fin.castSucc_castPred]
      · by_cases haTop : a = Fin.last k
        · rw [haTop] at ha
          exact False.elim ((not_lt_of_ge (Fin.le_last _)) ha)
        · obtain ⟨l, hl⟩ := hsurj (a.castPred haTop)
          refine ⟨⟨l.val, lt_trans l.isLt i.isLt⟩, ?_, ?_⟩
          · exact lt_of_lt_of_le l.isLt (Nat.le_of_not_gt hji)
          · rw [pgf_joinFirst_before, hl, Fin.castSucc_castPred]

private def pgf_rgJoinMap (n k : ℕ) :
    {d : pgfFirstData n k // IsSurjectiveRestrictedGrowthString d.2.1} →
      {w : Fin n → Fin (k + 1) // IsSurjectiveRestrictedGrowthString w} :=
  fun d => ⟨pgf_joinFirst d.val,
    (pgf_rg_join_iff d.val.1 d.val.2.1 d.val.2.2).2 d.property⟩

private lemma pgf_rgJoinMap_injective (n k : ℕ) :
    Function.Injective (pgf_rgJoinMap n k) := by
  intro d₁ d₂ h
  apply Subtype.ext
  apply pgf_joinFirst_injective n k
  simpa [pgf_rgJoinMap] using congrArg Subtype.val h

private lemma pgf_rgJoinMap_surjective (n k : ℕ) :
    Function.Surjective (pgf_rgJoinMap n k) := by
  intro w
  obtain ⟨z, hz⟩ := pgf_decodeFirst_surjective n k w
  cases z with
  | inl u =>
      obtain ⟨j, hj⟩ := w.property.1 (Fin.last k)
      have hc := congrFun hz j
      simp only [pgf_decodeFirst, Function.comp_apply] at hc
      exact False.elim (Fin.castSucc_ne_last _ (hc.trans hj))
  | inr d =>
      have hz' : pgf_joinFirst d = w := by simpa [pgf_decodeFirst] using hz
      have hdjoin : IsSurjectiveRestrictedGrowthString (pgf_joinFirst d) := by
        rw [hz']
        exact w.property
      let d' : {d : pgfFirstData n k // IsSurjectiveRestrictedGrowthString d.2.1} :=
        ⟨d, (pgf_rg_join_iff d.1 d.2.1 d.2.2).1 hdjoin⟩
      refine ⟨d', ?_⟩
      apply Subtype.ext
      simpa [pgf_rgJoinMap] using hz'

private noncomputable def pgf_rgJoinEquiv (n k : ℕ) :
    {d : pgfFirstData n k // IsSurjectiveRestrictedGrowthString d.2.1} ≃
      {w : Fin n → Fin (k + 1) // IsSurjectiveRestrictedGrowthString w} :=
  Equiv.ofBijective (pgf_rgJoinMap n k)
    ⟨pgf_rgJoinMap_injective n k, pgf_rgJoinMap_surjective n k⟩

private noncomputable def pgf_PH (k : ℕ) : pgfR :=
  PowerSeries.mk fun n =>
    ∑ d ∈ Finset.univ.filter
      (fun d : pgfFirstData n k => IsSurjectiveRestrictedGrowthString d.2.1),
      (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst d)

private lemma pgf_PP_succ_eq_PH (k : ℕ) : pgf_PP (k + 1) = pgf_PH k := by
  apply PowerSeries.ext
  intro n
  simp only [pgf_PP, pgf_PH, PowerSeries.coeff_mk]
  rw [Finset.sum_subtype (p := fun w : Fin n → Fin (k + 1) =>
      IsSurjectiveRestrictedGrowthString w) (Finset.univ.filter
    (fun w : Fin n → Fin (k + 1) => IsSurjectiveRestrictedGrowthString w)) (by simp)
    (fun w => (Polynomial.X : Polynomial ℤ) ^ pgf_peak w)]
  rw [← Equiv.sum_comp (pgf_rgJoinEquiv n k)
    (fun w => (Polynomial.X : Polynomial ℤ) ^ pgf_peak w.val)]
  change (∑ d : {d : pgfFirstData n k // IsSurjectiveRestrictedGrowthString d.2.1},
    (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst d.val)) = _
  rw [← Finset.sum_subtype (p := fun d : pgfFirstData n k =>
      IsSurjectiveRestrictedGrowthString d.2.1) (Finset.univ.filter
    (fun d : pgfFirstData n k => IsSurjectiveRestrictedGrowthString d.2.1)) (by simp)
    (fun d => (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst d))]

private lemma pgf_rg_base_sum (n k : ℕ) :
    (∑ i : Fin (n + 1), ∑ uv :
        (Fin i.val → Fin k) × (Fin (n + 1 - 1 - i.val) → Fin (k + 1)),
      if IsSurjectiveRestrictedGrowthString uv.1 then
        (Polynomial.X : Polynomial ℤ) ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
      else 0) =
      ∑ j ∈ Finset.range (n + 1),
        PowerSeries.coeff j (pgf_PP k) * PowerSeries.coeff (n - j) (pgf_W (k + 1)) := by
  apply Finset.sum_bij (s := Finset.univ) (t := Finset.range (n + 1))
    (fun i _ => i.val)
  · intro i _
    exact Finset.mem_range.mpr i.isLt
  · intro i₁ _ i₂ _ h
    exact Fin.ext h
  · intro j hj
    refine ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_univ _, rfl⟩
  · intro i _
    simp only [pgf_PP, pgf_W, PowerSeries.coeff_mk]
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : IsSurjectiveRestrictedGrowthString u <;> simp [hu]

private lemma pgf_rg_domain_pos {n k : ℕ} (u : Fin n → Fin (k + 1))
    (hu : IsSurjectiveRestrictedGrowthString u) : 0 < n := by
  obtain ⟨j, _⟩ := hu.1 (0 : Fin (k + 1))
  exact lt_of_le_of_lt (Nat.zero_le j.val) j.isLt

private lemma pgf_L_zero : pgf_L 0 = 0 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [pgf_L]
  | succ n =>
      simp only [pgf_L, PowerSeries.coeff_mk, Nat.zero_lt_succ, dite_true]
      apply Finset.sum_eq_zero
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      have hw0 := Fin.eq_zero (w ⟨0, Nat.zero_lt_succ n⟩)
      have hlast := Fin.eq_zero (Fin.last 0)
      rw [hw0, hlast] at hw
      exact False.elim ((lt_irrefl _) hw)

private lemma pgf_rg_boundary_sum_coeff (n k : ℕ) (i : Fin (n + 1)) :
    (∑ uv : (Fin i.val → Fin (k + 1)) ×
        (Fin (n + 1 - 1 - i.val) → Fin (k + 2)),
      if IsSurjectiveRestrictedGrowthString uv.1 then
        if pgf_boundary ⟨i, uv⟩ = 1 then
          (Polynomial.X : Polynomial ℤ) ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
        else 0
      else 0) =
      PowerSeries.coeff i.val (pgf_PP (k + 1)) *
        PowerSeries.coeff (n - i.val) (pgf_L (k + 1)) := by
  simp only [pgf_PP, pgf_L, PowerSeries.coeff_mk]
  rw [Fintype.sum_prod_type]
  by_cases hi : 0 < i.val
  · by_cases hv : 0 < n - i.val
    · simp only [dite_eq_left hv]
      rw [Finset.sum_mul_sum]
      simp_rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : IsSurjectiveRestrictedGrowthString u
      · simp only [hu, ↓reduceIte]
        apply Finset.sum_congr rfl
        intro v _
        by_cases hb : v ⟨0, hv⟩ < Fin.last (k + 1)
        · simp [pgf_boundary, hi, hv, hb]
        · simp [pgf_boundary, hi, hv, hb]
      · simp [hu]
    · simp only [dite_eq_right hv, mul_zero]
      apply Finset.sum_eq_zero
      intro u _
      apply Finset.sum_eq_zero
      intro v _
      simp [pgf_boundary, hi, hv]
  · have hPP :
        (∑ u ∈ Finset.univ.filter
          (fun u : Fin i.val → Fin (k + 1) => IsSurjectiveRestrictedGrowthString u),
          (Polynomial.X : Polynomial ℤ) ^ pgf_peak u) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      exact False.elim (hi (pgf_rg_domain_pos u hu))
    rw [hPP, zero_mul]
    apply Finset.sum_eq_zero
    intro u _
    apply Finset.sum_eq_zero
    intro v _
    by_cases hu : IsSurjectiveRestrictedGrowthString u
    · exact False.elim (hi (pgf_rg_domain_pos u hu))
    · simp [hu]

private lemma pgf_rg_boundary_sum (n k : ℕ) :
    (∑ i : Fin (n + 1), ∑ uv :
        (Fin i.val → Fin (k + 1)) × (Fin (n + 1 - 1 - i.val) → Fin (k + 2)),
      if IsSurjectiveRestrictedGrowthString uv.1 then
        if pgf_boundary ⟨i, uv⟩ = 1 then
          (Polynomial.X : Polynomial ℤ) ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
        else 0
      else 0) =
      ∑ j ∈ Finset.range (n + 1),
        PowerSeries.coeff j (pgf_PP (k + 1)) *
          PowerSeries.coeff (n - j) (pgf_L (k + 1)) := by
  apply Finset.sum_bij (s := Finset.univ) (t := Finset.range (n + 1))
    (fun i _ => i.val)
  · intro i _
    exact Finset.mem_range.mpr i.isLt
  · intro i₁ _ i₂ _ h
    exact Fin.ext h
  · intro j hj
    refine ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_univ _, rfl⟩
  · intro i _
    exact pgf_rg_boundary_sum_coeff n k i

private lemma pgf_rg_join_weight {n k : ℕ} (i : Fin n)
    (uv : (Fin i.val → Fin k) × (Fin (n - 1 - i.val) → Fin (k + 1))) :
    (if IsSurjectiveRestrictedGrowthString uv.1 then
      (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst ⟨i, uv⟩)
    else 0) =
      (if IsSurjectiveRestrictedGrowthString uv.1 then
        Polynomial.X ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
      else 0) +
      (Polynomial.X - 1) *
        (if IsSurjectiveRestrictedGrowthString uv.1 then
          if pgf_boundary ⟨i, uv⟩ = 1 then
            Polynomial.X ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
          else 0
        else 0) := by
  by_cases hu : IsSurjectiveRestrictedGrowthString uv.1
  · simp only [hu, ↓reduceIte]
    exact pgf_join_weight_data ⟨i, uv⟩
  · simp [hu]

private lemma pgf_PH_positive_recurrence (k : ℕ) :
    pgf_PH (k + 1) = pgf_x *
      (pgf_PP (k + 1) * pgf_W (k + 2) +
        (pgf_q - 1) * (pgf_PP (k + 1) * pgf_L (k + 1))) := by
  apply PowerSeries.ext
  intro s
  cases s with
  | zero => simp [pgf_PH, pgf_x]
  | succ n =>
      simp only [pgf_PH, PowerSeries.coeff_mk, pgf_x,
        PowerSeries.coeff_succ_X_mul, map_add]
      rw [Finset.sum_filter]
      rw [show pgf_q - 1 = PowerSeries.C ((Polynomial.X : Polynomial ℤ) - 1) by
        simp [pgf_q]]
      rw [PowerSeries.coeff_C_mul]
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      rw [Fintype.sum_sigma]
      calc
        (∑ i : Fin (n + 1), ∑ uv :
            (Fin i.val → Fin (k + 1)) ×
              (Fin (n + 1 - 1 - i.val) → Fin (k + 2)),
          if IsSurjectiveRestrictedGrowthString uv.1 then
            (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst ⟨i, uv⟩)
          else 0) =
            (∑ i : Fin (n + 1), ∑ uv :
              (Fin i.val → Fin (k + 1)) ×
                (Fin (n + 1 - 1 - i.val) → Fin (k + 2)),
              if IsSurjectiveRestrictedGrowthString uv.1 then
                Polynomial.X ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
              else 0) +
            (Polynomial.X - 1) *
              (∑ i : Fin (n + 1), ∑ uv :
                (Fin i.val → Fin (k + 1)) ×
                  (Fin (n + 1 - 1 - i.val) → Fin (k + 2)),
                if IsSurjectiveRestrictedGrowthString uv.1 then
                  if pgf_boundary ⟨i, uv⟩ = 1 then
                    Polynomial.X ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
                  else 0
                else 0) := by
          simp_rw [pgf_rg_join_weight, Finset.sum_add_distrib, Finset.mul_sum]
        _ = _ := by rw [pgf_rg_base_sum, pgf_rg_boundary_sum]

private lemma pgf_peak_fin_one {n : ℕ} (w : Fin n → Fin 1) : pgf_peak w = 0 := by
  unfold pgf_peak
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  have hnot (a b : Fin 1) : ¬a < b := by
    rw [Fin.eq_zero a, Fin.eq_zero b]
    exact lt_irrefl _
  simp [pgf_isPeakAt, hnot]

private lemma pgf_PP_one : pgf_PP 1 = pgf_x * pgf_W 1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp only [pgf_PP, pgf_x, PowerSeries.coeff_mk]
      rw [PowerSeries.coeff_zero_X_mul]
      apply Finset.sum_eq_zero
      intro w hw
      have hsurj := (Finset.mem_filter.mp hw).2.1
      obtain ⟨j, _⟩ := hsurj (0 : Fin 1)
      exact Fin.elim0 j
  | succ n =>
      simp only [pgf_x, PowerSeries.coeff_succ_X_mul, pgf_PP, pgf_W,
        PowerSeries.coeff_mk]
      rw [Finset.filter_eq_self.mpr]
      · simp_rw [pgf_peak_fin_one]
        simp
      · intro w _
        constructor
        · intro b
          refine ⟨0, ?_⟩
          exact Fin.eq_zero (w 0) |>.trans (Fin.eq_zero b).symm
        · intro i a h
          have ha := Fin.eq_zero a
          have hwi := Fin.eq_zero (w i)
          rw [ha, hwi] at h
          omega

private noncomputable def pgf_F (j : ℕ) : pgfR :=
  1 + pgf_x * (1 - pgf_q) * pgf_W j + pgf_q * (pgf_W j - 1)

private lemma pgf_F_eq (j : ℕ) :
    pgf_F j = pgf_W j + (pgf_q - 1) *
      (pgf_W j - 1 - pgf_x * pgf_W j) := by
  unfold pgf_F
  ring

private lemma pgf_F_one : pgf_F 1 = pgf_W 1 := by
  rw [pgf_F_eq, ← pgf_L_eq 0, pgf_L_zero]
  ring

private lemma pgf_PP_one_factor : pgf_PP 1 = pgf_x * pgf_F 1 := by
  rw [pgf_PP_one, pgf_F_one]

private lemma pgf_PP_succ_recurrence (k : ℕ) :
    pgf_PP (k + 2) = pgf_x * pgf_PP (k + 1) * pgf_F (k + 2) := by
  calc
    pgf_PP (k + 2) = pgf_PH (k + 1) := by
      simpa [Nat.add_assoc] using pgf_PP_succ_eq_PH (k + 1)
    _ = pgf_x * (pgf_PP (k + 1) * pgf_W (k + 2) +
          (pgf_q - 1) * (pgf_PP (k + 1) * pgf_L (k + 1))) :=
      pgf_PH_positive_recurrence k
    _ = pgf_x * pgf_PP (k + 1) * pgf_F (k + 2) := by
      rw [pgf_F_eq, pgf_L_eq]
      ring

private lemma pgf_PP_next (k : ℕ) (hk : 1 ≤ k) :
    pgf_PP (k + 1) = pgf_x * pgf_PP k * pgf_F (k + 1) := by
  have h1 : k - 1 + 1 = k := by omega
  have h2 : k - 1 + 2 = k + 1 := by omega
  simpa only [h1, h2] using pgf_PP_succ_recurrence (k - 1)

private lemma pgf_PP_product (k : ℕ) (hk : 1 ≤ k) :
    pgf_PP k = pgf_x ^ k * ∏ j ∈ Finset.Icc 1 k, pgf_F j := by
  induction k, hk using Nat.le_induction with
  | base =>
      rw [pgf_PP_one_factor]
      simp
  | succ k hk ih =>
      rw [pgf_PP_next k hk, ih]
      rw [Finset.prod_Icc_succ_top (by omega)]
      rw [pow_succ]
      ring

private noncomputable def pgf_r (j : ℕ) : pgfK :=
  pgf_map (pgf_G (j + 1)) / pgf_map (pgf_G j)

private lemma pgf_r_sub_B_ne_zero (j : ℕ) : pgf_r j - pgf_map pgf_B ≠ 0 := by
  have hg := pgf_map_G_ne_zero j
  have hd := pgf_map_den_ne_zero j
  unfold pgf_map at hg hd
  unfold pgf_den at hd
  unfold pgf_r pgf_map at ⊢
  simp only [map_sub, map_mul] at hd
  intro hr
  apply hd
  calc
    algebraMap pgfR pgfK (pgf_G (j + 1)) -
        algebraMap pgfR pgfK pgf_B * algebraMap pgfR pgfK (pgf_G j) =
        (algebraMap pgfR pgfK (pgf_G (j + 1)) /
          algebraMap pgfR pgfK (pgf_G j) - algebraMap pgfR pgfK pgf_B) *
            algebraMap pgfR pgfK (pgf_G j) := by field_simp
    _ = 0 := by rw [hr, zero_mul]

private lemma pgf_map_F (j : ℕ) :
    pgf_map (pgf_F j) =
      (1 - pgf_map pgf_q) *
        (1 + pgf_map pgf_x + pgf_map pgf_x ^ 2 * (1 - pgf_map pgf_q) - pgf_r j) /
        (1 + pgf_map pgf_x * (1 - pgf_map pgf_q) - pgf_r j) := by
  have hd := pgf_r_sub_B_ne_zero j
  have hB : pgf_map pgf_B = 1 + pgf_map pgf_x * (1 - pgf_map pgf_q) := by
    unfold pgf_B pgf_map
    simp only [map_sub, map_one, map_mul]
    ring
  have hd' : 1 + pgf_map pgf_x * (1 - pgf_map pgf_q) - pgf_r j ≠ 0 := by
    rw [← hB]
    exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hd))
  have hW : pgf_map (pgf_W j) = pgf_map pgf_A / (pgf_r j - pgf_map pgf_B) := by
    simpa only [pgf_r] using pgf_W_ratio j
  have hA : pgf_map pgf_A = pgf_map pgf_x * (pgf_map pgf_q - 1) := by
    unfold pgf_A pgf_map
    simp only [map_mul, map_sub, map_one]
  unfold pgf_F
  change algebraMap pgfR pgfK
      (1 + pgf_x * (1 - pgf_q) * pgf_W j + pgf_q * (pgf_W j - 1)) = _
  simp only [map_add, map_mul, map_sub, map_one]
  unfold pgf_map at hW hA hB hd hd' ⊢
  rw [hW]
  rw [hA]
  field_simp [hd, hd']
  rw [hB]
  ring

private lemma pgf_r_eq_U (j : ℕ) :
    pgf_r j =
      (pgf_U (j : ℤ) - pgf_U ((j : ℤ) - 1)) /
        (pgf_U ((j : ℤ) - 1) - pgf_U ((j : ℤ) - 2)) := by
  unfold pgf_r
  rw [pgf_G_eq_U_diff, pgf_G_eq_U_diff]
  have h0 : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
  have h1 : ((j + 1 : ℕ) : ℤ) - 2 = (j : ℤ) - 1 := by omega
  rw [h0, h1]

private lemma pgf_map_PP_closed (k : ℕ) (hk : 1 ≤ k) :
    pgf_map (pgf_PP k) =
      pgf_map pgf_x ^ k * (1 - pgf_map pgf_q) ^ k * ∏ j ∈ Finset.Icc 1 k,
        (1 + pgf_map pgf_x + pgf_map pgf_x ^ 2 * (1 - pgf_map pgf_q) -
          (pgf_U (j : ℤ) - pgf_U ((j : ℤ) - 1)) /
            (pgf_U ((j : ℤ) - 1) - pgf_U ((j : ℤ) - 2))) /
        (1 + pgf_map pgf_x * (1 - pgf_map pgf_q) -
          (pgf_U (j : ℤ) - pgf_U ((j : ℤ) - 1)) /
            (pgf_U ((j : ℤ) - 1) - pgf_U ((j : ℤ) - 2))) := by
  calc
    pgf_map (pgf_PP k) = pgf_map
        (pgf_x ^ k * ∏ j ∈ Finset.Icc 1 k, pgf_F j) := by rw [pgf_PP_product k hk]
    _ = pgf_map pgf_x ^ k * ∏ j ∈ Finset.Icc 1 k, pgf_map (pgf_F j) := by
      unfold pgf_map
      rw [map_mul, map_pow, map_prod]
    _ = _ := by
      simp_rw [pgf_map_F, pgf_r_eq_U]
      simp_rw [mul_div_assoc]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
      have hcard : k + 1 - 1 = k := by omega
      rw [hcard]
      ring

private lemma pgf_PP_triples (k : ℕ) :
    PowerSeries.mk (fun n => ∑ w ∈ Finset.univ.filter
      (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
      Polynomial.X ^ pgf_peakTriples w) = pgf_PP k := by
  apply PowerSeries.ext
  intro n
  simp only [pgf_PP, PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro w _
  rw [pgf_peakTriples_eq_peak]

/--
**Peak generating function for set partitions.** Let $k \ge 1$. Work in the fraction field of
the ring $\mathbb{Z}[q][[x]]$ of power series in $x$ with coefficients in $\mathbb{Z}[q]$. For
a word $w = w_0 \cdots w_{n-1}$, let $\mathrm{pk}(w)$ be the number of positions $a$ with
$a + 2 < n$ and $w_a < w_{a+1} > w_{a+2}$, and let $W_{n,k}$ be the set of surjective
restricted-growth strings of length $n$ with letters in $\{0, \dots, k-1\}$. Let
$t = 1 + x^2 (1-q)/2$, let $U_m = U_m(t)$ for $m \in \mathbb{Z}$, where $U_m$ is the Chebyshev
polynomial of the second kind extended to negative indices by its recurrence (so $U_{-1} = 0$
and $U_{-2} = -1$), and let $R_j = (U_j - U_{j-1})/(U_{j-1} - U_{j-2})$. Then
$$\sum_{n \ge 0} \sum_{w \in W_{n,k}} q^{\mathrm{pk}(w)} x^n = x^k (1-q)^k \prod_{j=1}^{k}
\frac{1 + x + x^2 (1-q) - R_j}{1 + x (1-q) - R_j}.$$

Set partitions of $\{1, \dots, n\}$ with $k$ blocks are encoded by the strings in $W_{n,k}$, and
$\mathrm{pk}(w)$ counts the peaks of the encoded partition. Division is total in the fraction
field, so the statement carries no nonvanishing hypotheses.

Proves `Wanted` entry `peak_generating_function_set_partitions`.

Proof: Following Mansour and Shattuck, Lemmas 2.1, 2.2, and 2.6 and Theorem 2.7,
the proof combines first-occurrence decompositions with the Chebyshev recurrence.

Source: Toufik Mansour and Mark Shattuck, "Counting Peaks and Valleys in
a Partition of a Set," Journal of Integer Sequences 13 (2010),
Article 10.6.8, Theorem (label th_peak_part), lines 313–317,
<https://cs.uwaterloo.ca/journals/JIS/VOL13/Shattuck/shattuck3.tex>.
-/
public theorem peak_generating_function_set_partitions
    (k : ℕ) (hk : 1 ≤ k)
    (t x q : FractionRing (PowerSeries (Polynomial ℤ)))
    (hx : x = algebraMap (PowerSeries (Polynomial ℤ))
      (FractionRing (PowerSeries (Polynomial ℤ))) PowerSeries.X)
    (hq : q = algebraMap (PowerSeries (Polynomial ℤ))
      (FractionRing (PowerSeries (Polynomial ℤ))) (PowerSeries.C Polynomial.X))
    (ht : t = 1 + x ^ 2 * (1 - q) / 2) :
    let U : ℤ → FractionRing (PowerSeries (Polynomial ℤ)) := fun m =>
      (Polynomial.Chebyshev.U (FractionRing (PowerSeries (Polynomial ℤ))) m).eval t
    algebraMap (PowerSeries (Polynomial ℤ))
      (FractionRing (PowerSeries (Polynomial ℤ)))
      (PowerSeries.mk (fun n => ∑ w ∈ Finset.univ.filter
        (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
        Polynomial.X ^ (Finset.filter
          (fun s : Fin n × Fin n × Fin n =>
            s.1.val + 1 = s.2.1.val ∧ s.2.1.val + 1 = s.2.2.val ∧
            w s.1 < w s.2.1 ∧ w s.2.2 < w s.2.1) Finset.univ).card)) =
    x ^ k * (1 - q) ^ k * ∏ j ∈ Finset.Icc 1 k,
      (1 + x + x ^ 2 * (1 - q) -
        (U (j : ℤ) - U ((j : ℤ) - 1)) / (U ((j : ℤ) - 1) - U ((j : ℤ) - 2))) /
      (1 + x * (1 - q) -
        (U (j : ℤ) - U ((j : ℤ) - 1)) / (U ((j : ℤ) - 1) - U ((j : ℤ) - 2))) := by
  dsimp only
  subst x
  subst q
  subst t
  change pgf_map (PowerSeries.mk (fun n => ∑ w ∈ Finset.univ.filter
    (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
    Polynomial.X ^ pgf_peakTriples w)) = _
  rw [pgf_PP_triples]
  simpa [pgf_map, pgf_x, pgf_q, pgf_t, pgf_U] using pgf_map_PP_closed k hk

end MetaMathlibExt
