/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Matroid.CharacteristicPolynomial
public import MathlibExt.Combinatorics.Matroid.ChowRing
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Order.Fin.InsertNth
import Mathlib.Order.Fin.Tuple

/-!
# Reduced characteristic polynomial coefficients as mixed degrees

For a finite loopless matroid, `reducedCharPolyCoeff_eq_deg` identifies the unsigned
coefficients of its reduced characteristic polynomial with the mixed degrees of the classes
`alphaClass` and `betaClass` in its Chow ring (Adiprasito, Huh and Katz, *Hodge theory for
combinatorial geometries*, Proposition 9.5).

Group the alternating subset sum by closure. Pairing subsets that differ by a fixed element
expresses the weight of a flat in terms of its lower covers missing that element. In the Chow
ring, multiplication by β extends a flag through precisely these covers, while multiplication
by α completes the upper part of the flag. The degree map gives each completed flag degree one.
-/

noncomputable section

open MathlibExt.Combinatorics.Matroid.Chow
open MathlibExt.Combinatorics.MatroidReducedCharacteristicPolynomialWanted
open MathlibExt.Combinatorics.MatroidCharacteristicPolynomialLogConcaveAMR156Problem0026Wanted
namespace MathlibExt.Combinatorics.MatroidHodgeTheoryWanted

section

variable {α : Type*} (M : _root_.Matroid α) [M.Finite]

private abbrev Flat := {F : Set α // M.IsFlat F}

private instance flatFinite : Finite (Flat M) := by
  have : Finite {S : Set α // S ⊆ M.E} := M.ground_finite.finite_subsets.to_subtype
  exact Finite.of_injective (fun F : Flat M =>
    (⟨F.1, F.2.subset_ground⟩ : {S : Set α // S ⊆ M.E}))
      (fun _ _ h => Subtype.ext (by simpa using congrArg Subtype.val h))

private instance flatFintype : Fintype (Flat M) := Fintype.ofFinite _
private instance properFintype : Fintype (ProperFlat M) := Fintype.ofFinite _

private def cl (X : Set α) : Flat M := ⟨M.closure X, M.isFlat_closure X⟩

private theorem rk_mono {X Y : Set α} (h : X ⊆ Y) : finRank M X ≤ finRank M Y :=
  ENat.toNat_le_toNat (M.eRk_mono h) (M.isRkFinite_set Y).eRk_lt_top.ne

private theorem rk_strict {F G : Set α} (hf : M.IsFlat F) (hg : M.IsFlat G)
    (h : F ⊂ G) : finRank M F < finRank M G := by
  by_contra! hn
  apply h.ne
  rw [← hf.closure, ← hg.closure]
  apply (M.isRkFinite_set F).closure_eq_closure_of_subset_of_eRk_ge_eRk h.le
  simpa [finRank, ENat.natCast_toNat, (M.isRkFinite_set _).eRk_lt_top.ne] using
    (show ((finRank M G : ℕ) : ℕ∞) ≤ (finRank M F : ℕ) from by exact_mod_cast hn)

open Classical in
private theorem rk_lift {e : α} (he : e ∈ M.E) (F : Flat M) :
    finRank M (cl M (insert e F.1)).1 =
      if e ∈ F.1 then finRank M F.1 else finRank M F.1 + 1 := by
  classical
  simp only [finRank, cl, M.eRk_closure_eq]
  split_ifs with h
  · rw [Set.insert_eq_of_mem h]
  · rw [Matroid.eRk_insert_eq_add_one ⟨he, by rwa [F.2.closure]⟩,
      ENat.toNat_add (M.isRkFinite_set _).eRk_lt_top.ne (by simp)]
    rfl

/-- The signed sum of subsets with a prescribed closure. -/
private def weight (F : Flat M) : ℤ := by
  classical
  exact ∑ I ∈ M.ground_finite.toFinset.powerset,
    if cl M I = F then (-1) ^ I.card else 0

private theorem weight_sum (f : Flat M → ℤ) :
    ∑ F, weight M F * f F =
      ∑ I ∈ M.ground_finite.toFinset.powerset, (-1) ^ I.card * f (cl M I) := by
  classical
  simp only [weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul]

-- Inserting a fixed element pairs subsets of opposite signs with the same lifted closure.
private theorem lift_cancel {e : α} (he : e ∈ M.E) (f : Flat M → ℤ) :
    ∑ F : Flat M, weight M F * f (cl M (insert e F.1)) = 0 := by
  classical
  rw [weight_sum]
  let E := M.ground_finite.toFinset
  have he' : e ∈ E := M.ground_finite.mem_toFinset.mpr he
  let g (I : Finset α) := (-1 : ℤ) ^ I.card * f (cl M (insert e (cl M I).1))
  change ∑ I ∈ E.powerset, g I = 0
  rw [← Finset.insert_erase he', Finset.sum_powerset_insert (Finset.notMem_erase _ _),
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro I hI
  have hn : e ∉ I := fun h => Finset.notMem_erase e E (Finset.mem_powerset.mp hI h)
  have hp : cl M (insert e (cl M (↑(insert e I) : Set α)).1) =
      cl M (insert e (cl M (I : Set α)).1) := by
    apply Subtype.ext
    simp [cl]
  simp only [g, hp, Finset.card_insert_of_notMem hn, pow_succ, mul_neg_one, neg_mul,
    add_neg_cancel]

private theorem lift_eq_iff {e : α} (he : e ∈ M.E) {F G : Flat M}
    (heF : e ∈ F.1) (heG : e ∉ G.1) :
    cl M (insert e G.1) = F ↔ G.1 ⊆ F.1 ∧ finRank M G.1 + 1 = finRank M F.1 := by
  have hr := rk_lift M he G
  rw [ite_eq_right heG] at hr
  have hins : insert e G.1 ⊆ M.E := Set.insert_subset he G.2.subset_ground
  have hG := (Set.subset_insert e G.1).trans (M.subset_closure _ hins)
  constructor
  · rintro rfl
    exact ⟨hG, hr.symm⟩
  · rintro ⟨hs, hd⟩
    have hle : (cl M (insert e G.1)).1 ⊆ F.1 :=
      (M.closure_subset_closure (Set.insert_subset heF hs)).trans_eq F.2.closure
    apply Subtype.ext
    by_contra hne
    have := rk_strict M (cl M (insert e G.1)).2 F.2 (hle.ssubset_of_ne hne)
    omega

open Classical in
private theorem weight_rec {F : Flat M} {e : α} (he : e ∈ F.1) :
    weight M F = -(∑ G : Flat M, if e ∉ G.1 ∧ G.1 ⊆ F.1 ∧
      finRank M G.1 + 1 = finRank M F.1 then weight M G else 0) := by
  classical
  have heE := F.2.subset_ground he
  have h := lift_cancel M heE (fun H => if H = F then 1 else 0)
  have split (G : Flat M) :
      weight M G * (if cl M (insert e G.1) = F then 1 else 0) =
        (if G = F then weight M G else 0) + (if e ∉ G.1 ∧ G.1 ⊆ F.1 ∧
          finRank M G.1 + 1 = finRank M F.1 then weight M G else 0) := by
    by_cases hG : e ∈ G.1
    · have ht : cl M (insert e G.1) = G :=
        Subtype.ext (by simp [cl, Set.insert_eq_of_mem hG, G.2.closure])
      rw [ht]
      simp [hG]
    · have hn : G ≠ F := fun h => hG (h ▸ he)
      simp [lift_eq_iff M heE he hG, hG, hn, mul_ite]
  simp only [split, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h
  omega

private theorem coeff_partial (k : ℕ) (hk : k < finRank M M.E) :
    reducedCharPolyCoeff M k = (-1) ^ k * ∑ F : Flat M,
      weight M F * (if finRank M F.1 ≤ k then 1 else 0) := by
  classical
  rw [reducedCharPolyCoeff, weight_sum]
  congr 1
  simp only [charPolyCoeff, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  have hIE : (I : Set α) ⊆ M.E := by simpa using Finset.mem_powerset.mp hI
  have hr := rk_mono M hIE
  have hr' : finRank M (cl M I).1 = finRank M I := by simp [cl, finRank]
  rw [hr']
  have hiff (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
      (finRank M M.E - finRank M I = finRank M M.E - j) ↔ j = finRank M I := by
    have := Finset.mem_range.mp hj
    omega
  calc
    _ = ∑ j ∈ Finset.range (k + 1), if j = finRank M I then (-1 : ℤ) ^ I.card else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [hiff j hj]
    _ = _ := by simp [Finset.sum_ite_eq', mul_ite]

open Classical in
private theorem coeff_flats {e : α} (he : e ∈ M.E) (k : ℕ) (hk : k < finRank M M.E) :
    reducedCharPolyCoeff M k = (-1) ^ k * ∑ F : Flat M,
      if e ∉ F.1 ∧ finRank M F.1 = k then weight M F else 0 := by
  classical
  rw [coeff_partial M k hk]
  congr 1
  have h := lift_cancel M he (fun F => if finRank M F.1 ≤ k then 1 else 0)
  apply eq_of_sub_eq_zero
  refine Eq.trans ?_ h
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro F _
  rw [rk_lift M he F]
  by_cases hF : e ∈ F.1
  · simp [hF]
  · simp [hF]
    split_ifs <;> omega

private def ofProper (F : ProperFlat M) : Flat M := ⟨F.1, F.2.1⟩

private theorem sum_proper {A : Type*} [AddCommMonoid A] (f : Flat M → A)
    (h : ∀ F, f F ≠ 0 → F.1.Nonempty ∧ F.1 ≠ M.E) :
    ∑ F : Flat M, f F = ∑ F : ProperFlat M, f (ofProper M F) := by
  classical
  symm
  apply Finset.sum_bij_ne_zero (fun F _ _ => ofProper M F)
  · simp
  · intro F _ _ G _ _ h
    exact Subtype.ext (congrArg (fun H : Flat M => H.1) h)
  · intro F _ hF
    obtain ⟨hn, hp⟩ := h F hF
    exact ⟨⟨F.1, F.2, hn, hp⟩, Finset.mem_univ _, hF, rfl⟩
  · simp

omit [M.Finite] in
private theorem rk_empty : finRank M ∅ = 0 := by simp [finRank]

variable [M.Loopless]

omit [M.Finite] in
private theorem empty_flat : M.IsFlat ∅ := by
  rw [Matroid.isFlat_iff_closure_eq, Matroid.closure_empty, M.loops_eq_empty]

private def botFlat : Flat M := ⟨∅, empty_flat M⟩

private theorem rk_zero_iff (F : Flat M) : finRank M F.1 = 0 ↔ F = botFlat M := by
  constructor
  · intro h
    apply Subtype.ext
    by_contra hn
    have := rk_strict M (empty_flat M) F.2
      ((Set.empty_subset F.1).ssubset_of_ne (Ne.symm hn))
    rw [rk_empty, h] at this
    omega
  · rintro rfl
    exact rk_empty M

private theorem weight_bot : weight M (botFlat M) = 1 := by
  classical
  unfold weight
  have h (I : Finset α) (hI : I ∈ M.ground_finite.toFinset.powerset) :
      cl M I = botFlat M ↔ I = ∅ := by
    constructor
    · intro he
      have hs : (I : Set α) ⊆ M.E := by simpa using Finset.mem_powerset.mp hI
      have hz : M.closure (I : Set α) = ∅ := congrArg Subtype.val he
      simpa using (M.subset_closure _ hs).trans_eq hz
    · rintro rfl
      apply Subtype.ext
      simp [cl, botFlat, Matroid.closure_empty]
  rw [Finset.sum_congr rfl (fun I hI => if_congr (h I hI) rfl rfl)]
  simp

omit [M.Loopless] in
open Classical in
private theorem alpha_sum (e : α) : alphaClass M e =
    ∑ F : ProperFlat M, if e ∈ F.1 then x M F else 0 := by
  classical
  simp [alphaClass, x, finsum_eq_sum_of_fintype, finsum_eq_if, apply_ite]

omit [M.Loopless] in
open Classical in
private theorem beta_sum (e : α) : betaClass M e =
    ∑ F : ProperFlat M, if e ∉ F.1 then x M F else 0 := by
  classical
  simp [betaClass, x, finsum_eq_sum_of_fintype, finsum_eq_if, apply_ite]

omit [M.Loopless] in
open Classical in
private theorem expand_alpha {i e : α} (hi : i ∈ M.E) (he : e ∈ M.E)
    (a : ℕ) (v : ChowRing M) :
    alphaClass M i ^ (a + 1) * v =
      ∑ G : ProperFlat M, if e ∈ G.1 then alphaClass M i ^ a * x M G * v else 0 := by
  classical
  calc
    _ = (alphaClass M i ^ a * alphaClass M e) * v := by rw [← alphaClass_eq M hi he, pow_succ]
    _ = _ := by rw [alpha_sum M e]; simp [Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul]

omit [M.Loopless] in
open Classical in
private theorem expand_beta {i e : α} (hi : i ∈ M.E) (he : e ∈ M.E)
    (a : ℕ) (v : ChowRing M) :
    betaClass M i ^ (a + 1) * v =
      ∑ G : ProperFlat M, if e ∉ G.1 then betaClass M i ^ a * x M G * v else 0 := by
  classical
  calc
    _ = (betaClass M i ^ a * betaClass M e) * v := by rw [← betaClass_eq M hi he, pow_succ]
    _ = _ := by rw [beta_sum M e]; simp [Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul]

omit [M.Loopless] in
private theorem alpha_nil {i : α} (hi : i ∈ M.E) (a : ℕ) (F : ProperFlat M)
    (ha : finRank M M.E ≤ finRank M F.1 + a) : alphaClass M i ^ a * x M F = 0 := by
  classical
  induction a generalizing F with
  | zero =>
    have := rk_strict M F.2.1 M.ground_isFlat (F.2.1.subset_ground.ssubset_of_ne F.2.2.2)
    omega
  | succ a ih =>
    obtain ⟨e, he, hn⟩ := Set.not_subset.mp
      (fun h => F.2.2.2 (Set.Subset.antisymm F.2.1.subset_ground h))
    rw [expand_alpha M hi he]
    apply Finset.sum_eq_zero
    intro G _
    by_cases heG : e ∈ G.1
    · simp only [ite_eq_left heG]
      by_cases hs : F.1 ⊆ G.1
      · have hr := rk_strict M F.2.1 G.2.1 (hs.ssubset_of_ne (fun h => hn (h ▸ heG)))
        have hz := ih G (by omega)
        rw [hz, zero_mul]
      · rw [mul_assoc, x_mul_x_eq_zero_of_incomparable M (fun h => hn (h heG)) hs, mul_zero]
    · simp [heG]

private theorem beta_nil {i : α} (hi : i ∈ M.E) (b : ℕ) (F : ProperFlat M)
    (hb : finRank M F.1 ≤ b) : betaClass M i ^ b * x M F = 0 := by
  classical
  induction b generalizing F with
  | zero =>
    have := rk_strict M (empty_flat M) F.2.1 (Set.empty_ssubset.mpr F.2.2.1)
    rw [rk_empty] at this
    omega
  | succ b ih =>
    obtain ⟨e, he⟩ := F.2.2.1
    have heE := F.2.1.subset_ground he
    rw [expand_beta M hi heE]
    apply Finset.sum_eq_zero
    intro G _
    by_cases heG : e ∉ G.1
    · simp only [ite_eq_left heG]
      by_cases hs : G.1 ⊆ F.1
      · have hr := rk_strict M G.2.1 F.2.1 (hs.ssubset_of_ne (fun h => heG (h ▸ he)))
        have hz := ih G (by omega)
        rw [hz, zero_mul]
      · rw [mul_assoc, x_mul_x_eq_zero_of_incomparable M hs (fun h => heG (h he)), mul_zero]
    · simp [heG]

private def mon {n : ℕ} (f : Fin n → ProperFlat M) : ChowRing M := ∏ j, x M (f j)

omit [M.Finite] [M.Loopless] in
private theorem mon_incomp {n : ℕ} (f : Fin n → ProperFlat M) (j : Fin n) (G : ProperFlat M)
    (h₁ : ¬ G.1 ⊆ (f j).1) (h₂ : ¬ (f j).1 ⊆ G.1) : x M G * mon M f = 0 := by
  classical
  rw [mon, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), ← mul_assoc,
    x_mul_x_eq_zero_of_incomparable M h₁ h₂, zero_mul]

-- At the highest flat of a flag, only the closure of a one-element extension survives.
omit [M.Loopless] in
private theorem upper_step {i : α} (hi : i ∈ M.E) (F : Flat M) (a : ℕ)
    (ha : finRank M F.1 + a + 2 = finRank M M.E) (v : ChowRing M)
    (hv : ∀ G : ProperFlat M, ¬ G.1 ⊆ F.1 → ¬ F.1 ⊆ G.1 → x M G * v = 0) :
    ∃ G : ProperFlat M, F.1 ⊂ G.1 ∧ finRank M G.1 = finRank M F.1 + 1 ∧
      alphaClass M i ^ (a + 1) * v = alphaClass M i ^ a * (x M G * v) := by
  classical
  have hn : ¬ M.E ⊆ F.1 := by
    intro h
    have := rk_mono M h
    omega
  obtain ⟨e, he, heF⟩ := Set.not_subset.mp hn
  let G := cl M (insert e F.1)
  have hr : finRank M G.1 = finRank M F.1 + 1 := by simp [G, rk_lift, he, heF]
  have hs : insert e F.1 ⊆ G.1 := M.subset_closure _ (Set.insert_subset he F.2.subset_ground)
  have heG := hs (Set.mem_insert e F.1)
  have hFG : F.1 ⊂ G.1 :=
    ((Set.subset_insert e _).trans hs).ssubset_of_ne (fun h => heF (h ▸ heG))
  have hne : G.1 ≠ M.E := by intro h; rw [h] at hr; omega
  let P : ProperFlat M := ⟨G.1, G.2, ⟨e, heG⟩, hne⟩
  refine ⟨P, hFG, hr, ?_⟩
  rw [expand_alpha M hi he, Finset.sum_eq_single P]
  · simp [P, heG, mul_assoc]
  · intro H _ hHP
    by_cases heH : e ∈ H.1
    · simp only [ite_eq_left heH]
      by_cases hFH : F.1 ⊆ H.1
      · have hGH : G.1 ⊆ H.1 :=
          (M.closure_subset_closure (Set.insert_subset heH hFH)).trans_eq H.2.1.closure
        have hlt := rk_strict M G.2 H.2.1
          (hGH.ssubset_of_ne (fun h => hHP (Subtype.ext h.symm)))
        rw [alpha_nil M hi a H (by omega), zero_mul]
      · rw [mul_assoc, hv H (fun h => heF (h heH)) hFH, mul_zero]
    · simp [heH]
  · simp

private theorem weight_rank_one (F : Flat M) (hr : finRank M F.1 = 1) : weight M F = -1 := by
  classical
  have hn : F.1.Nonempty := Set.nonempty_iff_ne_empty.mpr (fun h => by
    rw [h, rk_empty] at hr
    omega)
  obtain ⟨e, he⟩ := hn
  rw [weight_rec M he, Finset.sum_eq_single (botFlat M)]
  · rw [weight_bot]
    simp [botFlat, rk_empty, hr]
  · intro G _ hG
    have := (rk_zero_iff M G).not.mpr hG
    have hn' : finRank M G.1 + 1 ≠ finRank M F.1 := by omega
    simp [hn']
  · simp

omit [M.Loopless] in
open Classical in
private theorem weight_rec_proper (F : Flat M) {e : α} (he : e ∈ F.1)
    (b : ℕ) (hb : finRank M F.1 = b + 2) :
    (weight M F : ℝ) = -∑ G : ProperFlat M, if e ∉ G.1 ∧ G.1 ⊆ F.1 ∧
      finRank M G.1 = b + 1 then (weight M (ofProper M G) : ℝ) else 0 := by
  classical
  let w (G : Flat M) : ℤ := if e ∉ G.1 ∧ G.1 ⊆ F.1 ∧ finRank M G.1 = b + 1
    then weight M G else 0
  have hw : weight M F = -∑ G : Flat M, w G := by
    rw [weight_rec M he, hb]
    simp [w]
  have hp := sum_proper M w (by
    intro G h
    obtain ⟨hn, hs, hG⟩ : e ∉ G.1 ∧ G.1 ⊆ F.1 ∧ finRank M G.1 = b + 1 := by
      by_contra hp
      exact h (ite_eq_right hp)
    constructor
    · apply Set.nonempty_iff_ne_empty.mpr
      intro hz
      rw [hz, rk_empty] at hG
      omega
    · intro hz
      exact hn (hz ▸ F.2.subset_ground he))
  rw [hp] at hw
  simpa only [w, ofProper, Int.cast_neg, Int.cast_sum, apply_ite, Int.cast_zero] using
    congrArg (fun z : ℤ => (z : ℝ)) hw

-- Extend a flag downwards. The surviving lower covers give the recurrence for its weight.
private theorem beta_flag {i : α} (hi : i ∈ M.E) {r : ℕ}
    {deg : ChowRing M →ₗ[ℝ] ℝ} (hd : IsDegreeMap M r deg)
    (b : ℕ) {n : ℕ} (f : Fin (n + 1) → ProperFlat M)
    (hf : StrictMono (fun j => (f j).1)) (hlen : n + 1 + b = r)
    (hb : finRank M (f 0).1 = b + 1) :
    deg (betaClass M i ^ b * mon M f) = (-1 : ℝ) ^ (b + 1) * weight M (ofProper M (f 0)) := by
  classical
  induction b generalizing n with
  | zero =>
    simp only [Nat.add_zero] at hlen
    subst r
    rw [pow_zero, one_mul, weight_rank_one M _ hb, mon, hd.2 f hf]
    norm_num
  | succ b ih =>
    let F := f 0
    obtain ⟨e, he⟩ := F.2.2.1
    have heE := F.2.1.subset_ground he
    have hrec := weight_rec_proper M (ofProper M F) he b hb
    rw [expand_beta M hi heE, map_sum]
    calc
      _ = ∑ G : ProperFlat M, (-1 : ℝ) ^ (b + 1) *
          (if e ∉ G.1 ∧ G.1 ⊆ F.1 ∧ finRank M G.1 = b + 1 then
            (weight M (ofProper M G) : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro G _
        by_cases heG : e ∉ G.1
        · by_cases hs : G.1 ⊆ F.1
          · have hlt : G.1 ⊂ F.1 := hs.ssubset_of_ne (fun h => heG (h ▸ he))
            by_cases hr : finRank M G.1 = b + 1
            · let g : Fin (n + 2) → ProperFlat M := Fin.cons G f
              have hmono : StrictMono (fun j => (g j).1) := by
                change StrictMono (Subtype.val ∘ Fin.cons G f)
                rw [Fin.comp_cons, Fin.strictMono_cons]
                exact ⟨fun j => hlt.trans_le (hf.monotone (Fin.zero_le j)), hf⟩
              have h := ih g hmono (by omega) (by simpa [g] using hr)
              have hmon : mon M g = x M G * mon M f := by
                rw [mon, Fin.prod_univ_succ]
                simp [mon, g]
              rw [hmon] at h
              simpa [heG, hs, hr, mul_assoc, g] using h
            · have hR := rk_strict M G.2.1 F.2.1 hlt
              have hF : finRank M F.1 = b + 2 := hb
              simp [heG, hs, hr, beta_nil M hi b G (by omega)]
          · have hz := mon_incomp M f 0 G hs (fun h => heG (h he))
            simp [heG, hs, mul_assoc, hz]
        · simp [heG]
      _ = _ := by
        rw [← Finset.mul_sum]
        change _ = (-1 : ℝ) ^ (b + 1 + 1) * (weight M (ofProper M F) : ℝ)
        rw [hrec, pow_succ (-1 : ℝ) (b + 1)]
        simp [ofProper]

-- Extend the same flag upwards until only the powers of β remain.
private theorem mixed_flag {i : α} (hi : i ∈ M.E) {r : ℕ}
    (hr : finRank M M.E = r + 1) {deg : ChowRing M →ₗ[ℝ] ℝ} (hd : IsDegreeMap M r deg)
    (a b : ℕ) {n : ℕ} (f : Fin (n + 1) → ProperFlat M)
    (hf : StrictMono (fun j => (f j).1)) (hlen : n + 1 + a + b = r)
    (hb : finRank M (f 0).1 = b + 1) (ht : finRank M (f (Fin.last n)).1 + a = r) :
    deg (betaClass M i ^ b * (alphaClass M i ^ a * mon M f)) =
      (-1 : ℝ) ^ (b + 1) * weight M (ofProper M (f 0)) := by
  classical
  induction a generalizing n with
  | zero => simpa using beta_flag M hi hd b f hf (by omega) hb
  | succ a ih =>
    let T := f (Fin.last n)
    obtain ⟨G, hTG, hG, hstep⟩ := upper_step M hi (ofProper M T) a (by
      change finRank M (f (Fin.last n)).1 + a + 2 = _
      omega) (mon M f) (mon_incomp M f (Fin.last n))
    let g : Fin (n + 2) → ProperFlat M := Fin.snoc f G
    have hg : StrictMono (fun j => (g j).1) := by
      change StrictMono (Subtype.val ∘ Fin.snoc f G)
      rw [Fin.comp_snoc]
      simpa only [Fin.insertNth_last'] using
        Fin.strictMono_insertNth_last (f := Subtype.val ∘ f) hf G.1 hTG
    have hmon : mon M g = x M G * mon M f := by
      rw [mon, Fin.prod_univ_castSucc]
      simp [g, mon, mul_comm]
    have hrG : finRank M G.1 = finRank M (f (Fin.last n)).1 + 1 := hG
    have h := ih g hg (by omega) (by simpa [g] using hb) (by
      simp only [g, Fin.snoc_last]
      omega)
    rw [hstep, ← hmon]
    simpa [g] using h

private theorem mixed_generator {i : α} (hi : i ∈ M.E) {r : ℕ}
    (hr : finRank M M.E = r + 1) {deg : ChowRing M →ₗ[ℝ] ℝ} (hd : IsDegreeMap M r deg)
    (a b : ℕ) (hab : a + b + 1 = r) (F : ProperFlat M) :
    deg (betaClass M i ^ b * (alphaClass M i ^ a * x M F)) =
      if finRank M F.1 = b + 1 then (-1 : ℝ) ^ (b + 1) * weight M (ofProper M F) else 0 := by
  classical
  split_ifs with h
  · let f : Fin 1 → ProperFlat M := fun _ => F
    have hf : StrictMono (fun j => (f j).1) := Subsingleton.strictMono _
    have := mixed_flag M hi hr hd a b (n := 0) f hf (by omega) h (by
      change finRank M F.1 + a = r
      omega)
    simpa [mon, f] using this
  · by_cases hF : finRank M F.1 ≤ b
    · rw [mul_left_comm, beta_nil M hi b F hF, mul_zero, map_zero]
    · rw [alpha_nil M hi a F (by omega), mul_zero, map_zero]

private theorem degree_alpha {i : α} (hi : i ∈ M.E) {r : ℕ}
    (hr : finRank M M.E = r + 1) {deg : ChowRing M →ₗ[ℝ] ℝ} (hd : IsDegreeMap M r deg) :
    deg (alphaClass M i ^ r) = 1 := by
  classical
  cases r with
  | zero =>
    have h := hd.2 (Fin.elim0 : Fin 0 → ProperFlat M) (Subsingleton.strictMono _)
    simpa using h
  | succ a =>
    obtain ⟨G, _, hG, hs⟩ := upper_step M hi (botFlat M) a (by
      change finRank M ∅ + a + 2 = finRank M M.E
      rw [rk_empty]; omega) 1 (by intro G _ h; exact (h (Set.empty_subset _)).elim)
    have hG' : finRank M G.1 = 1 := by simpa [botFlat, rk_empty] using hG
    have h := mixed_generator M hi hr hd a 0 (by omega) G
    simp only [mul_one] at hs
    rw [hs]
    simpa [hG', weight_rank_one M (ofProper M G) hG'] using h

end

/-- **Reduced characteristic polynomial coefficients as mixed degrees** (Adiprasito, Huh and
Katz, *Hodge theory for combinatorial geometries*, Ann. of Math. 188 (2018), Proposition 9.5).
For a finite loopless matroid `M` of rank `r + 1`, its degree map `deg`, any element `i` of the
ground set and every `k ≤ r`, `μ_k(M) = deg(α_M^{r-k} β_M^k)`, where `α_M` and `β_M` are the
classes of `∑_{i ∈ F} x_F` and `∑_{i ∉ F} x_F`. -/
public theorem reducedCharPolyCoeff_eq_deg {α : Type*} (M : _root_.Matroid α) [M.Finite]
    [M.Loopless] (r : ℕ) (hr : M.eRank = r + 1) (deg : ChowRing M →ₗ[ℝ] ℝ)
    (hdeg : IsDegreeMap M r deg) (i : α) (hi : i ∈ M.E) (k : ℕ) (hk : k ≤ r) :
    (reducedCharPolyCoeff M k : ℝ) = deg (alphaClass M i ^ (r - k) * betaClass M i ^ k) := by
  classical
  have hR : finRank M M.E = r + 1 := by simp [finRank, hr, ENat.toNat_add]
  rw [coeff_flats M hi k (by omega)]
  cases k with
  | zero =>
    rw [Finset.sum_eq_single (botFlat M)]
    · rw [weight_bot]
      simp [degree_alpha M hi hR hdeg, botFlat, rk_empty]
    · intro F _ hF
      simp [(rk_zero_iff M F).not.mpr hF]
    · simp
  | succ b =>
    let w (G : Flat M) := if i ∉ G.1 ∧ finRank M G.1 = b + 1 then weight M G else 0
    have hp := sum_proper M w (by
      intro G hn
      have hc : i ∉ G.1 ∧ finRank M G.1 = b + 1 := by
        by_contra h
        exact hn (ite_eq_right h)
      refine ⟨Set.nonempty_iff_ne_empty.mpr ?_, fun h => hc.1 (h ▸ hi)⟩
      intro h
      have := hc.2
      rw [h, rk_empty] at this
      omega)
    let a := r - (b + 1)
    change (((-1 : ℤ) ^ (b + 1) * ∑ G : Flat M, w G : ℤ) : ℝ) = _
    rw [hp]
    push_cast
    rw [mul_comm (alphaClass M i ^ _), expand_beta M hi hi, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro F _
    have h := mixed_generator M hi hR hdeg a b (by dsimp [a]; omega) F
    change (-1 : ℝ) ^ (b + 1) * (w (ofProper M F) : ℝ) =
      deg (if i ∉ F.1 then betaClass M i ^ b * x M F * alphaClass M i ^ a else 0)
    by_cases he : i ∈ F.1
    · simp [w, ofProper, he]
    · simpa [w, ofProper, he, mul_ite, apply_ite, mul_comm, mul_left_comm, mul_assoc] using h.symm

end MathlibExt.Combinatorics.MatroidHodgeTheoryWanted
