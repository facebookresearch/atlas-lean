/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.LorentzianPolynomials
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Analysis.Complex.Polynomial.GaussLucas

/-!
# Independence generating polynomials of matroids

The homogenised independence generating polynomial of a matroid is Lorentzian.
We use the recursive definition of Lorentzian polynomials. Differentiation in a matroid
variable contracts a nonloop, and differentiation in the homogenising variable leaves
a falling factorial on each coefficient. Matroid augmentation gives M-convexity of the support.

In degrees at most two, independence is determined by the parallel classes of the nonloops,
as in Anari, Liu, Oveis Gharan and Vinzant, *Log-concave polynomials III*, Lemma 4.2.
We obtain stability directly by applying Gauss–Lucas to a product of linear factors, one
for each class, padded with powers of the homogenising variable.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.LorentzianToolboxWanted

open Finsupp MvPolynomial
open scoped _root_.Matroid
open MathlibExt.Combinatorics.LorentzianPolynomialsWanted.LorentzianPolynomials
open MathlibExt.Combinatorics.Matroid.MConvex

variable {n : ℕ}

private noncomputable def exponent (d : ℕ) (A : Finset (Fin n)) : Fin (n + 1) →₀ ℕ :=
  single 0 (d - A.card) + indicatorVec (A.map (Fin.succEmb n))

@[simp] private lemma exponent_zero (d : ℕ) (A : Finset (Fin n)) : exponent d A 0 = d - A.card := by
  simp [exponent, indicatorVec_apply]

@[simp] private lemma exponent_succ (d : ℕ) (A : Finset (Fin n)) (i : Fin n) :
    exponent d A i.succ = if i ∈ A then 1 else 0 := by
  simp [exponent, indicatorVec_apply]

private lemma exponent_injective (d : ℕ) : Function.Injective (exponent (n := n) d) := by
  intro A B h
  ext i
  have hi : exponent d A i.succ = exponent d B i.succ := DFunLike.congr_fun h i.succ
  simp only [exponent_succ] at hi
  clear h
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp_all

private noncomputable def indepSets (M : _root_.Matroid (Fin n)) (d : ℕ) :
    Finset (Finset (Fin n)) :=
  open Classical in Finset.univ.filter fun A => M.Indep (A : Set (Fin n)) ∧ A.card ≤ d

@[simp] private lemma mem_indepSets {M : _root_.Matroid (Fin n)} {d : ℕ} {A : Finset (Fin n)} :
    A ∈ indepSets M d ↔ M.Indep (A : Set (Fin n)) ∧ A.card ≤ d := by classical simp [indepSets]

private def derivativeWeight (d k a : ℕ) : ℝ := ((d - a + k).descFactorial k : ℕ)

private lemma derivativeWeight_pos (d k a : ℕ) : 0 < derivativeWeight d k a := by
  unfold derivativeWeight
  exact_mod_cast Nat.descFactorial_pos.mpr (by omega : k ≤ d - a + k)

-- After k derivatives in the homogenising variable, d is the remaining degree.
-- Every independent set of size at most d contributes a strictly positive coefficient.
private noncomputable def derivativeForm (M : _root_.Matroid (Fin n)) (d k : ℕ) :
    MvPolynomial (Fin (n + 1)) ℝ :=
  ∑ A ∈ indepSets M d, monomial (exponent d A) (derivativeWeight d k A.card)

private lemma coeff_nonneg (M : _root_.Matroid (Fin n)) (d k : ℕ) (m) :
    0 ≤ (derivativeForm M d k).coeff m := by
  classical
  simp only [derivativeForm, coeff_sum, coeff_monomial]
  exact Finset.sum_nonneg fun A _ => by split <;> first | exact (derivativeWeight_pos ..).le | rfl

private lemma support_form (M : _root_.Matroid (Fin n)) (d k : ℕ) :
    (derivativeForm M d k).support = (indepSets M d).image (exponent d) := by
  classical
  ext m
  simp only [MvPolynomial.mem_support_iff, derivativeForm, coeff_sum, coeff_monomial]
  constructor
  · contrapose
    intro hm
    exact Finset.sum_eq_zero fun A hA =>
      ite_eq_right (fun h => hm (Finset.mem_image.mpr ⟨A, hA, h⟩))
  · rintro hm
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hm
    rw [Finset.sum_eq_single_of_mem A hA]
    · simpa using (derivativeWeight_pos d k A.card).ne'
    · intro B _ h
      exact ite_eq_right (fun he => h (exponent_injective d he))

-- Exchange with coordinate zero adds or removes a matroid element. For an exchange
-- between two matroid elements, augment the smaller independent set after erasing i.
private lemma convex_form (M : _root_.Matroid (Fin n)) (d k : ℕ) :
    MathlibExt.Combinatorics.Matroid.MConvex.IsMConvex
      ((derivativeForm M d k).support : Set (Fin (n + 1) →₀ ℕ)) := by
  classical
  rw [support_form]
  intro α hα β hβ i hi
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hα
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hβ
  obtain ⟨hAI, hAd⟩ := mem_indepSets.mp hA
  obtain ⟨hBI, hBd⟩ := mem_indepSets.mp hB
  cases i using Fin.cases with
  | zero =>
    simp only [exponent_zero] at hi
    obtain ⟨j, hjB, hjA, hJ⟩ := hAI.augment_finset hBI (by omega)
    refine ⟨j.succ, by simp [hjA, hjB], Finset.mem_image.mpr ⟨insert j A, ?_, ?_⟩⟩
    · exact mem_indepSets.mpr ⟨by simpa using hJ, by rw [Finset.card_insert_of_notMem hjA]; omega⟩
    · ext t
      cases t using Fin.cases with
      | zero => simp [Finset.card_insert_of_notMem hjA]; omega
      | succ t =>
        by_cases ht : j = t
        · subst t; simp [hjA]
        · simp [Ne.symm ht]
  | succ i =>
    simp only [exponent_succ] at hi
    have ha : i ∈ A := by by_contra h; simp [h] at hi
    have hb : i ∉ B := by intro h; simp [h, ha] at hi
    have hI : M.Indep (A.erase i : Finset (Fin n)) := hAI.subset (Finset.erase_subset ..)
    have hc := Finset.card_erase_add_one ha
    by_cases hlt : B.card < A.card
    · refine ⟨0, by simp; omega,
        Finset.mem_image.mpr ⟨A.erase i, mem_indepSets.mpr ⟨hI, by omega⟩, ?_⟩⟩
      ext t
      cases t using Fin.cases with
      | zero => simp; omega
      | succ t =>
        by_cases ht : i = t
        · subst t; simp [ha]
        · simp [Ne.symm ht]
    · obtain ⟨j, hjB, hjA, hJ⟩ := hI.augment_finset hBI (by omega)
      have hij : i ≠ j := fun h => hb (h ▸ hjB)
      have hj : j ∉ A := by simpa [Finset.mem_erase, hij.symm] using hjA
      refine ⟨j.succ, by simp [hj, hjB], Finset.mem_image.mpr ⟨insert j (A.erase i), ?_, ?_⟩⟩
      · exact mem_indepSets.mpr ⟨by simpa using hJ, by rw [Finset.card_insert_of_notMem hjA]; omega⟩
      · ext t
        cases t using Fin.cases with
        | zero => simp [Finset.card_insert_of_notMem hjA, hc]
        | succ t =>
          by_cases hi' : i = t
          · subst t; simp [ha, hij]
          · by_cases hj' : j = t
            · subst t; simp [hj, hij]
            · simp [Ne.symm hi', Ne.symm hj']

private lemma pderiv_zero (M : _root_.Matroid (Fin n)) (d k : ℕ) :
    pderiv 0 (derivativeForm M (d + 1) k) = derivativeForm M d (k + 1) := by
  classical
  simp only [derivativeForm, map_sum, pderiv_monomial, exponent_zero]
  have hsub : indepSets M d ⊆ indepSets M (d + 1) := fun _ h =>
    mem_indepSets.mpr ⟨(mem_indepSets.mp h).1, Nat.le_succ_of_le (mem_indepSets.mp h).2⟩
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro A hA
    have ha := (mem_indepSets.mp hA).2
    apply congrArg₂ (fun m r => monomial m r)
    · ext i
      cases i using Fin.cases <;> simp
      omega
    · unfold derivativeWeight
      rw [Nat.descFactorial_succ]
      push_cast
      rw [show d + 1 - A.card + k = d - A.card + (k + 1) by omega,
        show d - A.card + (k + 1) - k = d + 1 - A.card by omega, mul_comm]
  · intro A hA ha
    have hle := (mem_indepSets.mp hA).2
    have hn : ¬ A.card ≤ d := fun h => ha (mem_indepSets.mpr ⟨(mem_indepSets.mp hA).1, h⟩)
    simp [show d + 1 - A.card = 0 by omega]

private lemma pderiv_of_not_isNonloop (M : _root_.Matroid (Fin n)) (d k : ℕ) (i : Fin n)
    (hi : ¬ M.IsNonloop i) : pderiv i.succ (derivativeForm M (d + 1) k) = 0 := by
  classical
  simp only [derivativeForm, map_sum, pderiv_monomial, exponent_succ]
  apply Finset.sum_eq_zero
  intro A hA
  have h : i ∉ A := fun h => hi ((mem_indepSets.mp hA).1.isNonloop_of_mem h)
  simp [h]

private lemma pderiv_of_isNonloop (M : _root_.Matroid (Fin n)) (d k : ℕ) (i : Fin n)
    (hi : M.IsNonloop i) :
    pderiv i.succ (derivativeForm M (d + 1) k) = derivativeForm (M ／ {i}) d k := by
  classical
  simp only [derivativeForm, map_sum, pderiv_monomial, exponent_succ]
  rw [← Finset.sum_filter_of_ne (p := fun A => i ∈ A)]
  · refine Finset.sum_bij' (fun A _ => A.erase i) (fun B _ => insert i B) ?_ ?_ ?_ ?_ ?_
    · intro A hA
      obtain ⟨h, ha⟩ := Finset.mem_filter.mp hA
      obtain ⟨hind, hcard⟩ := mem_indepSets.mp h
      exact mem_indepSets.mpr ⟨hi.contractElem_indep_iff.mpr
        ⟨by simp, by simpa only [← Finset.coe_insert, Finset.insert_erase ha] using hind⟩,
        by have := Finset.card_erase_add_one ha; omega⟩
    · intro B hB
      obtain ⟨hI, hcard⟩ := mem_indepSets.mp hB
      obtain ⟨hiB, hind⟩ := hi.contractElem_indep_iff.mp hI
      exact Finset.mem_filter.mpr ⟨mem_indepSets.mpr ⟨by simpa using hind, by
        rw [Finset.card_insert_of_notMem hiB]; omega⟩, Finset.mem_insert_self ..⟩
    · intro A hA
      exact Finset.insert_erase (Finset.mem_filter.mp hA).2
    · intro B hB
      exact Finset.erase_insert (hi.contractElem_indep_iff.mp (mem_indepSets.mp hB).1).1
    · intro A hA
      have ha := (Finset.mem_filter.mp hA).2
      have hc := Finset.card_erase_add_one ha
      have he : d + 1 - A.card = d - (A.erase i).card := by omega
      simp only [ha, ite_true, Nat.cast_one, mul_one]
      apply congrArg₂ (fun m r => monomial m r)
      · ext t
        cases t using Fin.cases with
        | zero => simp [he]
        | succ t =>
          by_cases h : i = t
          · subst t; simp [ha]
          · simp [Ne.symm h]
      · simp [derivativeWeight, he]
  · intro A _ h
    contrapose h
    simp [h]

section Partition

variable {α β R : Type*} [CommSemiring R]

private noncomputable def selections (U : Finset α) (c : α → β) : Finset (Finset α) :=
  open Classical in U.powerset.filter fun A => Set.InjOn c A

private lemma mem_selections {U A : Finset α} {c : α → β} :
    A ∈ selections U c ↔ A ⊆ U ∧ Set.InjOn c A := by
  classical simp [selections]

-- Choosing one element in each fibre is equivalent to choosing a subset on which the
-- class map is injective and has the prescribed image.
open scoped Classical in
private lemma prod_fiber_sums (U : Finset α) (c : α → β) (s : Finset β) (w : α → R) :
    ∏ j ∈ s, (∑ i ∈ U.filter (fun i => c i = j), w i) =
      ∑ A ∈ (selections U c).filter (fun A => A.image c = s), ∏ i ∈ A, w i := by
  classical
  rw [Finset.prod_sum]
  let range (p : ∀ j ∈ s, α) := s.attach.image (fun j => p j.1 j.2)
  have entry {p : ∀ j ∈ s, α} (hp : p ∈ s.pi fun j => U.filter (fun i => c i = j))
      (j : β) (hj : j ∈ s) : p j hj ∈ U ∧ c (p j hj) = j :=
    Finset.mem_filter.mp (Finset.mem_pi.mp hp _ hj)
  have hr {p : ∀ j ∈ s, α} {i : α} : i ∈ range p ↔ ∃ j, ∃ h : j ∈ s, p j h = i := by
    simp [range]
  have h_image {p : ∀ j ∈ s, α} (hp : p ∈ s.pi fun j => U.filter (fun i => c i = j)) :
      (range p).image c = s := by
    ext j
    constructor
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨j, hs, rfl⟩ := hr.mp hi
      rw [(entry hp j hs).2]
      exact hs
    · intro hj
      exact Finset.mem_image.mpr ⟨_, hr.mpr ⟨j, hj, rfl⟩, (entry hp j hj).2⟩
  refine Finset.sum_bij (fun p _ => range p) ?_ ?_ ?_ ?_
  · intro p hp
    refine Finset.mem_filter.mpr ⟨mem_selections.mpr ⟨?_, ?_⟩, h_image hp⟩
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := hr.mp hi
      exact (entry hp j hj).1
    · intro i hi l hl he
      obtain ⟨j, hj, rfl⟩ := hr.mp hi
      obtain ⟨j', hj', rfl⟩ := hr.mp hl
      have h := (entry hp j hj).2.symm.trans (he.trans (entry hp j' hj').2)
      subst j'
      rfl
  · intro p hp q hq he
    funext j hj
    have h : p j hj ∈ range q := he ▸ hr.mpr ⟨j, hj, rfl⟩
    obtain ⟨j', hj', hh⟩ := hr.mp h
    have : j' = j := (entry hq j' hj').2.symm.trans ((congrArg c hh).trans (entry hp j hj).2)
    subst j'
    exact hh.symm
  · intro A hA
    obtain ⟨hA, him⟩ := Finset.mem_filter.mp hA
    obtain ⟨hU, hI⟩ := mem_selections.mp hA
    have exists_i (j) (hj : j ∈ s) : ∃ i ∈ A, c i = j := by
      rw [← him] at hj
      exact Finset.mem_image.mp hj
    choose p hmem hval using exists_i
    refine ⟨p, Finset.mem_pi.mpr (fun j hj => Finset.mem_filter.mpr
      ⟨hU (hmem j hj), hval j hj⟩), ?_⟩
    ext i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := hr.mp hi
      exact hmem j hj
    · intro hi
      have hj := him ▸ Finset.mem_image_of_mem c hi
      exact hr.mpr ⟨c i, hj, hI (hmem _ hj) hi (hval _ hj)⟩
  · intro p hp
    symm
    apply Finset.prod_image
    intro j _ j' _ he
    exact Subtype.ext ((entry hp j j.2).2.symm.trans ((congrArg c he).trans (entry hp j' j'.2).2))

-- The power of x pads the product to degree m when there are fewer than m classes.
open scoped Classical in
private lemma partition_expansion (U : Finset α) (c : α → β) (m : ℕ)
    (hm : (U.image c).card ≤ m) (x : R) (w : α → R) :
    (∏ j ∈ U.image c, ((∑ i ∈ U.filter (fun i => c i = j), w i) + x)) *
        x ^ (m - (U.image c).card) =
      ∑ A ∈ selections U c, (∏ i ∈ A, w i) * x ^ (m - A.card) := by
  classical
  let C := U.image c
  have hmaps (A) (hA : A ∈ selections U c) : A.image c ∈ C.powerset :=
    Finset.mem_powerset.mpr (Finset.image_mono c (mem_selections.mp hA).1)
  conv_rhs => rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  rw [Finset.prod_add (fun j => ∑ i ∈ U.filter (fun i => c i = j), w i) (fun _ => x),
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  have hsC := Finset.mem_powerset.mp hs
  rw [prod_fiber_sums, Finset.prod_const, Finset.card_sdiff_of_subset hsC, Finset.sum_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A hA
  obtain ⟨hsel, rfl⟩ := Finset.mem_filter.mp hA
  rw [Finset.card_image_of_injOn (s := A) (mem_selections.mp hsel).2]
  rw [mul_assoc, ← pow_add]
  have hcard := Finset.card_le_card hsC
  rw [Finset.card_image_of_injOn (s := A) (mem_selections.mp hsel).2] at hcard
  congr 2
  omega

end Partition

open scoped Polynomial UpperHalfPlane

-- By Gauss-Lucas, differentiation preserves exclusion of the open upper half plane.
private lemma nonvanishing_derivative (p : ℂ[X]) (k : ℕ) (hk : k ≤ p.natDegree)
    (hp : ∀ z : ℂ, 0 < z.im → p.eval z ≠ 0) :
    ∀ z : ℂ, 0 < z.im → (Polynomial.derivative^[k] p).eval z ≠ 0 := by
  induction k generalizing p with
  | zero => simpa using hp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have hpos : 0 < p.natDegree := by omega
    apply ih
    · rw [Polynomial.natDegree_derivative]
      omega
    · intro z hz he
      have hroots : p.rootSet ℂ ⊆ {w : ℂ | w.im ≤ 0} := by
        intro w hw
        change w.im ≤ 0
        apply le_of_not_gt
        intro hw'
        exact hp w hw' (by simpa using (Polynomial.mem_rootSet.mp hw).2)
      have hconv := convexHull_min hroots (convex_halfSpace_le Complex.imLm.isLinear 0)
      have hd := Polynomial.rootSet_derivative_subset_convexHull_rootSet
        (Polynomial.natDegree_pos_iff_degree_pos.mp hpos)
      exact hz.not_ge (hconv (hd (Polynomial.mem_rootSet.mpr
        ⟨Polynomial.derivative_ne_zero.mpr hpos.ne', by simpa using he⟩)))

private lemma eval_form (M : _root_.Matroid (Fin n)) (d k : ℕ) (z : Fin (n + 1) → ℍ) :
    aeval (((↑) : ℍ → ℂ) ∘ z) (derivativeForm M d k) =
      ∑ A ∈ indepSets M d, (∏ i ∈ A, (z i.succ : ℂ)) *
        ((derivativeWeight d k A.card : ℂ) * (z 0 : ℂ) ^ (d - A.card)) := by
  classical
  simp only [derivativeForm, map_sum]
  apply Finset.sum_congr rfl
  intro A _
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
  simp only [Function.comp_apply, exponent_zero, exponent_succ, Complex.coe_algebraMap]
  simp_rw [pow_ite, pow_one, pow_zero]
  rw [Fintype.prod_ite_mem]
  ring

-- On at most two elements, independence is equivalent to choosing nonloops
-- from distinct parallel classes. The closure of a singleton identifies its class.
private lemma small_indep (M : _root_.Matroid (Fin n)) (A : Finset (Fin n)) (hd : A.card ≤ 2) :
    M.Indep (A : Set (Fin n)) ↔
      (∀ i ∈ A, M.IsNonloop i) ∧ Set.InjOn (fun i => M.closure {i}) A := by
  classical
  constructor
  · intro h
    refine ⟨fun i hi => h.isNonloop_of_mem hi, ?_⟩
    intro i hi j hj he
    exact ((h.isNonloop_of_mem hi).closure_eq_closure_iff_eq_or_dep
      (h.isNonloop_of_mem hj)).mp he |>.resolve_right
        (fun hn => hn (h.subset (Set.insert_subset hi (Set.singleton_subset_iff.mpr hj))))
  · rintro ⟨h, hinj⟩
    have hc : A.card = 0 ∨ A.card = 1 ∨ A.card = 2 := by omega
    rcases hc with h0 | h1 | h2
    · rw [Finset.card_eq_zero.mp h0]
      simp
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
      simpa using (h i (by simp)).indep
    · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp h2
      have hi := h i (by simp)
      have hj := h j (by simp)
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.injOn_pair] at hinj ⊢
      by_contra hn
      exact hij (hinj ((hi.closure_eq_closure_iff_eq_or_dep hj).mpr (Or.inr hn)))

-- Fix the other variables in the upper half plane and write X for the homogenising variable.
-- In the padded product, the coefficient of X^(d + k - a) enumerates selections of size a.
-- After k derivatives only a ≤ d survives, so for d ≤ 2 these are precisely independent sets.
private lemma low_stable (M : _root_.Matroid (Fin n)) (d k : ℕ) (hd : d ≤ 2)
    (hsize : M.E.ncard ≤ d + k) : IsStable (derivativeForm M d k) := by
  classical
  right
  intro z
  let U := Finset.univ.filter M.IsNonloop
  let c (i : Fin n) := M.closure {i}
  let classes := U.image c
  let w (i : Fin n) : ℂ := z i.succ
  let v (j : Set (Fin n)) := ∑ i ∈ U.filter (fun i => c i = j), w i
  let P : ℂ[X] := (∏ j ∈ classes, (Polynomial.X + Polynomial.C (v j))) *
    Polynomial.X ^ (d + k - classes.card)
  have hU : U ⊆ M.E.toFinset := fun i hi =>
    Set.mem_toFinset.mpr ((Finset.mem_filter.mp hi).2.mem_ground)
  have hc : classes.card ≤ d + k := calc
    _ ≤ U.card := Finset.card_image_le
    _ ≤ M.E.toFinset.card := Finset.card_le_card hU
    _ ≤ _ := by simpa only [← Set.ncard_eq_toFinset_card'] using hsize
  have hdeg : P.natDegree = d + k := by
    dsimp only [P]
    rw [Polynomial.natDegree_mul ((Polynomial.monic_prod_of_monic _ _ (fun j _ =>
      Polynomial.monic_X_add_C (v j))).ne_zero) (pow_ne_zero _ Polynomial.X_ne_zero),
      Polynomial.natDegree_prod_of_monic (h := fun j _ => Polynomial.monic_X_add_C (v j))]
    simp [Nat.add_sub_of_le hc]
  have hp (t : ℂ) (ht : 0 < t.im) : P.eval t ≠ 0 := by
    simp only [P, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_X]
    apply mul_ne_zero (Finset.prod_ne_zero_iff.mpr ?_)
      (pow_ne_zero _ (fun he => by simp [he] at ht))
    intro j _
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    apply ne_of_apply_ne Complex.im
    simp only [Complex.add_im, Complex.zero_im, v, Complex.im_sum]
    exact (add_pos_of_pos_of_nonneg ht (Finset.sum_nonneg (fun i _ => (z i.succ).im_pos.le))).ne'
  have hP : P = ∑ A ∈ selections U c,
      Polynomial.C (∏ i ∈ A, w i) * Polynomial.X ^ (d + k - A.card) := by
    have hprod := partition_expansion U c (d + k) hc (Polynomial.X : ℂ[X])
      (fun i => Polynomial.C (w i))
    convert (by simpa only [← map_sum, ← map_prod, add_comm] using hprod) using 1
    dsimp only [P, classes, v]
    congr! 5
  have hsmall {A : Finset (Fin n)} (ha : A.card ≤ d) :
      A ∈ indepSets M d ↔ A ∈ selections U c := by
    rw [mem_indepSets, mem_selections, and_iff_left ha, small_indep _ _ (ha.trans hd)]
    apply and_congr_left
    intro _
    simp only [Finset.subset_iff, U, Finset.mem_filter, Finset.mem_univ, true_and]
  have hEval : ((Polynomial.derivative^[k] P).eval (z 0 : ℂ)) =
      aeval (((↑) : ℍ → ℂ) ∘ z) (derivativeForm M d k) := by
    rw [hP, Polynomial.iterate_derivative_sum, Polynomial.eval_finsetSum, eval_form]
    simp only [Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_X_pow_eq_C_mul,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    have hsub : indepSets M d ⊆ selections U c := fun _ h => (hsmall (mem_indepSets.mp h).2).mp h
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro A hA
      have ha := (mem_indepSets.mp hA).2
      simp only [derivativeWeight, Complex.ofReal_natCast, w]
      rw [show d + k - A.card = d - A.card + k by omega, Nat.add_sub_cancel]
    · intro A hA hnot
      have hlt : d < A.card := by
        by_contra! h
        exact hnot ((hsmall h).mpr hA)
      have hAc : A.card ≤ d + k := by
        rw [← Finset.card_image_of_injOn (mem_selections.mp hA).2]
        exact (Finset.card_le_card (Finset.image_mono c (mem_selections.mp hA).1)).trans hc
      have hz : (d + k - A.card).descFactorial k = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp [hz]
  rw [← hEval]
  exact nonvanishing_derivative P k (by omega) hp (z 0) (z 0).im_pos

private lemma zero_mem_L (m : ℕ) : ∀ d (g : H m d), g.1 = 0 → g ∈ L m d
  | 0, g, hg | 1, g, hg | 2, g, hg => ⟨Or.inl hg, by simp [hg]⟩
  | d + 3, g, hg => by
    refine ⟨⟨?_, by simp [hg]⟩, fun i => zero_mem_L m (d + 2) _ ?_⟩
    · intro α hα
      simp [hg] at hα
    · simp [hg]

private lemma form_mem_L : ∀ (d k : ℕ) (M : _root_.Matroid (Fin n)),
    M.E.ncard ≤ d + k → ∀ (g : H (n + 1) d), g.1 = derivativeForm M d k → g ∈ L (n + 1) d
  | 0, k, M, hm, g, hg | 1, k, M, hm, g, hg | 2, k, M, hm, g, hg =>
    ⟨hg ▸ low_stable M _ k (by decide) hm, hg ▸ coeff_nonneg M _ k⟩
  | d + 3, k, M, hm, g, hg => by
    refine ⟨⟨hg ▸ convex_form M _ k, hg ▸ coeff_nonneg M _ k⟩, ?_⟩
    intro i
    cases i using Fin.cases with
    | zero =>
      apply form_mem_L (d + 2) (k + 1) M (by omega)
      change pderiv 0 g.1 = _
      rw [hg, pderiv_zero]
    | succ i =>
      by_cases hi : M.IsNonloop i
      · have hc := Set.ncard_sdiff_singleton_add_one hi.mem_ground
        apply form_mem_L (d + 2) k (M ／ {i}) (by rw [Matroid.contract_ground]; omega)
        change pderiv i.succ g.1 = _
        rw [hg, pderiv_of_isNonloop _ _ _ _ hi]
      · apply zero_mem_L
        change pderiv i.succ g.1 = 0
        rw [hg, pderiv_of_not_isNonloop _ _ _ _ hi]

open scoped Classical in
/-- **Independence generating polynomials of matroids are Lorentzian** (Brändén and Huh,
*Lorentzian polynomials*, Ann. of Math. 192 (2020), proof of Theorem 4.14, from Theorem 4.10).
For a matroid `M` on `[n]`, the homogeneous polynomial
`f_M(w_0, w_1, …, w_n) = ∑_{A independent} w^A w_0^{n - |A|}` of degree `n` in `n + 1` variables
lies in `L (n + 1) n`. Here `w_0` is the variable `0 : Fin (n + 1)` and `w_i` is `i.succ`. -/
theorem independenceGeneratingPolynomial_mem_L {n : ℕ} (M : _root_.Matroid (Fin n))
    (g : H (n + 1) n)
    (hg : g.1 = ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin n) => M.Indep (A : Set (Fin n))),
      monomial (single 0 (n - A.card) + indicatorVec (A.map (Fin.succEmb n))) (1 : ℝ)) :
    g ∈ L (n + 1) n := by
  classical
  apply form_mem_L n 0 M (by simpa using M.E.ncard_le_card) g
  rw [hg]
  have hcard (A : Finset (Fin n)) : A.card ≤ n := by simpa using A.card_le_univ
  simp [derivativeForm, indepSets, derivativeWeight, exponent, hcard]

end MathlibExt.Combinatorics.LorentzianToolboxWanted
