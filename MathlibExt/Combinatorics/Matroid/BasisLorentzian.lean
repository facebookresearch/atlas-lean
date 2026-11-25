/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.LorentzianPolynomials
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Combinatorics.Matroid.Minor.Contract
public import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Basis generating polynomials of matroids are Lorentzian

The basis generating polynomial of a matroid is Lorentzian: differentiation in a
variable contracts a nonloop, and in degrees at most two the polynomial is stable,
with the quadratic case following from Gauss–Lucas applied to the product over the
parallel classes. The main result is `basisGeneratingPolynomial_mem_L`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.LorentzianToolboxWanted

open Finsupp MvPolynomial
open scoped _root_.Matroid Polynomial UpperHalfPlane
open MathlibExt.Combinatorics.LorentzianPolynomialsWanted.LorentzianPolynomials
open MathlibExt.Combinatorics.Matroid.MConvex

variable {n : ℕ}

/-- **The bases of a matroid**, as a finset of finsets. -/
private noncomputable def bases (M : _root_.Matroid (Fin n)) : Finset (Finset (Fin n)) :=
  open Classical in Finset.univ.filter fun B => M.IsBase (B : Set (Fin n))

@[simp] private lemma mem_bases {M : _root_.Matroid (Fin n)} {B : Finset (Fin n)} :
    B ∈ bases M ↔ M.IsBase (B : Set (Fin n)) := by classical simp [bases]

/-- **The basis generating polynomial** of a matroid on `[n]`: the sum, over its bases
`B`, of the square-free monomial `∏_{i ∈ B} w_i`. -/
private noncomputable def basisForm (M : _root_.Matroid (Fin n)) : MvPolynomial (Fin n) ℝ :=
  ∑ B ∈ bases M, monomial (indicatorVec B) (1 : ℝ)

/-- A base of a matroid of rank `d` has `d` elements. -/
private lemma base_card {M : _root_.Matroid (Fin n)} {d : ℕ} (hd : M.eRank = d)
    {B : Finset (Fin n)} (hB : M.IsBase (B : Set (Fin n))) : B.card = d := by
  have h := hB.encard_eq_eRank
  rw [hd] at h
  rw [Set.encard_coe_eq_coe_finsetCard] at h
  exact_mod_cast h

private lemma coeff_basisForm_nonneg (M : _root_.Matroid (Fin n)) (m) :
    0 ≤ (basisForm M).coeff m := by
  classical
  simp only [basisForm, coeff_sum, coeff_monomial]
  exact Finset.sum_nonneg fun B _ => by split <;> first | rfl | exact zero_le_one

private lemma support_basisForm (M : _root_.Matroid (Fin n)) :
    (basisForm M).support = (bases M).image indicatorVec := by
  classical
  ext m
  simp only [MvPolynomial.mem_support_iff, basisForm, coeff_sum, coeff_monomial]
  constructor
  · contrapose
    intro hm
    exact Finset.sum_eq_zero fun B hB =>
      ite_eq_right (fun h => hm (Finset.mem_image.mpr ⟨B, hB, h⟩))
  · rintro hm
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hm
    rw [Finset.sum_eq_single_of_mem B hB]
    · simp
    · intro C _ h
      exact ite_eq_right (fun he => h (indicatorVec_injective he))

/-- The support of the basis generating polynomial is the set of base vectors, which is
M-convex by the base exchange axiom. -/
private lemma convex_basisForm (M : _root_.Matroid (Fin n)) :
    MathlibExt.Combinatorics.Matroid.MConvex.IsMConvex
      ((basisForm M).support : Set (Fin n →₀ ℕ)) := by
  rw [support_basisForm]
  have : ((bases M).image indicatorVec : Set (Fin n →₀ ℕ)) = baseVectors M := by
    ext α
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, baseVectors]
    constructor
    · rintro ⟨B, hB, rfl⟩
      exact ⟨B, mem_bases.mp hB, rfl⟩
    · rintro ⟨B, hB, rfl⟩
      exact ⟨B, mem_bases.mpr hB, rfl⟩
  rw [this]
  exact isMConvex_baseVectors M

/-- Removing `i ∈ B` from the indicator vector of `B` gives the indicator vector of
`B.erase i`. -/
private lemma indicatorVec_erase {B : Finset (Fin n)} {i : Fin n} (hi : i ∈ B) :
    indicatorVec B - single i 1 = indicatorVec (B.erase i) := by
  ext k
  simp only [Finsupp.tsub_apply, indicatorVec_apply, Finset.mem_erase, single_apply]
  by_cases hki : i = k
  · subst hki
    simp [hi]
  · have hkk : ¬k = i := fun h => hki h.symm
    simp [hki, hkk]

/-- A base containing `i` exists only when `i` is a nonloop. -/
private lemma not_mem_base_of_not_isNonloop {M : _root_.Matroid (Fin n)} {i : Fin n}
    (hi : ¬ M.IsNonloop i) {B : Finset (Fin n)} (hB : M.IsBase (B : Set (Fin n))) :
    i ∉ B := by
  intro hmem
  apply hi
  exact (hB.indep.subset (Set.singleton_subset_iff.mpr hmem)).isNonloop_of_mem (by simp)

/-- Differentiating the basis generating polynomial: only bases containing `i`
contribute, with `i` removed. -/
private lemma pderiv_basisForm (M : _root_.Matroid (Fin n)) (i : Fin n) :
    pderiv i (basisForm M) =
      ∑ B ∈ (bases M).filter (i ∈ ·), monomial (indicatorVec (B.erase i)) (1 : ℝ) := by
  classical
  simp only [basisForm, map_sum, pderiv_monomial, indicatorVec_apply]
  rw [← Finset.sum_filter_of_ne (p := fun B => i ∈ B)]
  · apply Finset.sum_congr rfl
    intro B hB
    have hi : i ∈ B := (Finset.mem_filter.mp hB).2
    simp only [hi, ite_true, Nat.cast_one, mul_one]
    rw [indicatorVec_erase hi]
  · intro B hB hne
    by_contra hi
    apply hne
    simp [hi]

/-- Bases of the contraction by a nonloop, as finsets. -/
private lemma mem_bases_contract_iff {M : _root_.Matroid (Fin n)} {i : Fin n}
    (hi : M.IsNonloop i) {B : Finset (Fin n)} :
    B ∈ bases (M ／ {i}) ↔ M.IsBase (insert i B : Finset (Fin n)) ∧ i ∉ B := by
  rw [mem_bases]
  constructor
  · intro hB
    obtain ⟨hbase, hdisj⟩ := hi.indep.contract_isBase_iff.mp hB
    have heq : (B : Set (Fin n)) ∪ {i} = (insert i B : Finset (Fin n)) := by
      ext x
      simp
    rw [heq] at hbase
    refine ⟨hbase, ?_⟩
    have := hdisj
    rw [Set.disjoint_singleton_right] at this
    exact this
  · rintro ⟨hbase, hiB⟩
    have heq : (B : Set (Fin n)) ∪ {i} = (insert i B : Finset (Fin n)) := by
      ext x
      simp
    rw [← heq] at hbase
    exact hi.indep.contract_isBase_iff.mpr ⟨hbase, Set.disjoint_singleton_right.mpr hiB⟩

/-- Differentiating in a nonloop variable gives the basis generating polynomial of
the contraction. -/
private lemma pderiv_basisForm_of_isNonloop (M : _root_.Matroid (Fin n)) (i : Fin n)
    (hi : M.IsNonloop i) :
    pderiv i (basisForm M) = basisForm (M ／ {i}) := by
  classical
  rw [pderiv_basisForm]
  refine Finset.sum_bij' (fun B _ => B.erase i) (fun B _ => insert i B) ?_ ?_ ?_ ?_ ?_
  · intro B hB
    rw [Finset.mem_filter] at hB
    have hmem : M.IsBase (B : Set (Fin n)) := mem_bases.mp hB.1
    have hiB : i ∈ B := hB.2
    rw [mem_bases_contract_iff hi]
    exact ⟨by simpa [Finset.insert_erase hiB] using hmem, by simp⟩
  · intro B hB
    rw [mem_bases_contract_iff hi] at hB
    exact Finset.mem_filter.mpr ⟨mem_bases.mpr hB.1, Finset.mem_insert_self ..⟩
  · intro B hB
    rw [Finset.mem_filter] at hB
    exact Finset.insert_erase hB.2
  · intro B hB
    rw [mem_bases_contract_iff hi] at hB
    exact Finset.erase_insert hB.2
  · intro B hB
    rfl

/-- Differentiating in a loop variable, or in a variable outside the ground set, gives
zero: no base contains such an element. -/
private lemma pderiv_basisForm_of_not_isNonloop (M : _root_.Matroid (Fin n)) (i : Fin n)
    (hi : ¬ M.IsNonloop i) : pderiv i (basisForm M) = 0 := by
  classical
  rw [pderiv_basisForm]
  apply Finset.sum_eq_zero
  intro B hB
  rw [Finset.mem_filter] at hB
  exact absurd hB.2 (not_mem_base_of_not_isNonloop hi (mem_bases.mp hB.1))

/-- Contracting a nonloop drops the rank by one. -/
private lemma eRank_contract {M : _root_.Matroid (Fin n)} {i : Fin n} (hi : M.IsNonloop i) :
    (M ／ {i}).eRank + 1 = M.eRank := by
  obtain ⟨B, hB⟩ := (M ／ {i}).exists_isBase
  obtain ⟨hbase, hdisj⟩ := hi.indep.contract_isBase_iff.mp hB
  have h2 := hbase.encard_eq_eRank
  have h3 := hB.encard_eq_eRank
  rw [← h2, ← h3, Set.encard_union_eq hdisj]
  simp

/-- Contracting a nonloop from a matroid of rank `d` leaves rank `d - 1`. -/
private lemma eRank_contract_eq {M : _root_.Matroid (Fin n)} {i : Fin n}
    (hi : M.IsNonloop i) {d : ℕ} (hd : M.eRank = d) :
    (M ／ {i}).eRank = d - 1 := by
  have h := eRank_contract hi
  rw [hd] at h
  have hne : (M ／ {i}).eRank ≠ ⊤ := by
    intro htop
    rw [htop] at h
    simp at h
  rw [← ENat.natCast_toNat hne]
  congr 1
  have h3 := congrArg ENat.toNat h
  rw [ENat.toNat_add hne (by simp), ENat.toNat_natCast, ENat.toNat_one] at h3
  omega

private lemma zero_mem_L (m : ℕ) : ∀ d (g : H m d), g.1 = 0 → g ∈ L m d
  | 0, g, hg | 1, g, hg | 2, g, hg => ⟨Or.inl hg, by simp [hg]⟩
  | d + 3, g, hg => by
    refine ⟨⟨?_, by simp [hg]⟩, fun i => zero_mem_L m (d + 2) _ ?_⟩
    · intro α hα
      simp [hg] at hα
    · simp [hg]

open scoped Polynomial UpperHalfPlane in
/-- Evaluating the basis generating polynomial at a point of the upper half-plane:
the sum over bases of the product of the coordinates. -/
private lemma eval_basisForm (M : _root_.Matroid (Fin n)) (z : Fin n → ℍ) :
    aeval (((↑) : ℍ → ℂ) ∘ z) (basisForm M) =
      ∑ B ∈ bases M, ∏ i ∈ B, (z i : ℂ) := by
  classical
  simp only [basisForm, map_sum, aeval_monomial]
  apply Finset.sum_congr rfl
  intro B _
  have hsupp : (indicatorVec B).support = B := by
    ext i
    simp [indicatorVec_apply]
  rw [Finsupp.prod, hsupp]
  simp only [map_one, one_mul]
  apply Finset.prod_congr rfl
  intro i hi
  simp [indicatorVec_apply, hi]

/-- **The nonloops** of a matroid, as a finset. -/
private noncomputable abbrev nonloops (M : _root_.Matroid (Fin n)) : Finset (Fin n) :=
  open Classical in Finset.univ.filter M.IsNonloop

/-- **The parallel class** of an element: the closure of its singleton. -/
private def parClass (M : _root_.Matroid (Fin n)) (i : Fin n) : Set (Fin n) :=
  M.closure {i}

/-- **The parallel classes** of a matroid: the closures of the singletons of its
nonloops. -/
private noncomputable def parClasses (M : _root_.Matroid (Fin n)) : Finset (Set (Fin n)) :=
  (nonloops M).image (parClass M)

/-- **The class sum** of a parallel class at a point of the upper half-plane: the sum
of the coordinates of the nonloops in that class. -/
private noncomputable def classSum (M : _root_.Matroid (Fin n)) (z : Fin n → ℍ)
    (C : Set (Fin n)) : ℂ :=
  ∑ i ∈ (nonloops M).filter (fun i => parClass M i = C), (z i : ℂ)

section ProdFiber

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

end ProdFiber

/-- On at most two elements, independence is equivalent to choosing nonloops from
distinct parallel classes, as in Anari, Liu, Oveis Gharan and Vinzant,
*Log-concave polynomials III*, Lemma 4.2. -/
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

/-- Every matroid on a finite type has a base given by a finset. -/
private lemma exists_finset_isBase (M : _root_.Matroid (Fin n)) :
    ∃ B : Finset (Fin n), M.IsBase (B : Set (Fin n)) := by
  obtain ⟨B₀, hB₀⟩ := M.exists_isBase
  exact ⟨(Set.toFinite B₀).toFinset, by simpa using hB₀⟩

/-- **Degree zero.** A matroid of rank `0` has the empty set as its only base, so its
basis generating polynomial is `1`. -/
private lemma stable_zero {M : _root_.Matroid (Fin n)} (hd : M.eRank = 0) :
    IsStable (basisForm M) := by
  classical
  obtain ⟨B₀, hB₀⟩ := M.exists_isBase
  have henc : B₀.encard = 0 := by
    rw [hB₀.encard_eq_eRank, hd]
  have hB₀eq : B₀ = ∅ := Set.encard_eq_zero.mp henc
  have hbasis : bases M = {∅} := by
    ext B
    simp only [mem_bases, Finset.mem_singleton]
    constructor
    · intro hB
      have := base_card hd hB
      exact Finset.card_eq_zero.mp this
    · intro hB
      rw [hB]
      have : ((∅ : Finset (Fin n)) : Set (Fin n)) = ∅ := by simp
      rw [this, ← hB₀eq]
      exact hB₀
  have hform : basisForm M = 1 := by
    have h0 : indicatorVec (∅ : Finset (Fin n)) = 0 := by
      ext i
      simp [indicatorVec_apply]
    simp only [basisForm, hbasis, Finset.sum_singleton, h0, MvPolynomial.monomial_zero',
      MvPolynomial.C_1]
  right
  intro z
  rw [hform]
  simp

/-- **Degree one.** The basis generating polynomial is a sum of distinct variables,
which cannot vanish on the upper half-plane. -/
private lemma stable_one {M : _root_.Matroid (Fin n)} (hd : M.eRank = 1) :
    IsStable (basisForm M) := by
  classical
  right
  intro z
  have hpos : 0 < (aeval (((↑) : ℍ → ℂ) ∘ z) (basisForm M)).im := by
    rw [eval_basisForm, Complex.im_sum]
    obtain ⟨B₀, hB₀⟩ := exists_finset_isBase M
    apply Finset.sum_pos
    · intro B hB
      have hcard : B.card = 1 := base_card hd (mem_bases.mp hB)
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
      simpa using (z i).im_pos
    · exact ⟨B₀, mem_bases.mpr hB₀⟩
  exact ne_of_apply_ne Complex.im (by simpa using hpos.ne')

/-- A class sum has positive imaginary part: the class is nonempty and every
coordinate lies in the upper half-plane. -/
private lemma classSum_im_pos {M : _root_.Matroid (Fin n)} {z : Fin n → ℍ}
    {C : Set (Fin n)} (hC : C ∈ parClasses M) : 0 < (classSum M z C).im := by
  have hC' : C ∈ (nonloops M).image (parClass M) := hC
  obtain ⟨i, hiU, rfl⟩ := Finset.mem_image.mp hC'
  unfold classSum
  rw [Complex.im_sum]
  apply Finset.sum_pos
  · intro j _
    simpa using (z j).im_pos
  · exact ⟨i, Finset.mem_filter.mpr ⟨hiU, rfl⟩⟩

/-- **Evaluating a rank-two basis generating polynomial.** Its value is the second
elementary symmetric function of the parallel class sums: a base is a pair of
nonloops from distinct parallel classes. -/
private lemma eval_basisForm_two {M : _root_.Matroid (Fin n)} (hd : M.eRank = 2)
    (z : Fin n → ℍ) :
    aeval (((↑) : ℍ → ℂ) ∘ z) (basisForm M) =
      ∑ t ∈ (parClasses M).powersetCard 2, ∏ C ∈ t, classSum M z C := by
  classical
  rw [eval_basisForm]
  have hmaps : ∀ B ∈ bases M, B.image (parClass M) ∈ (parClasses M).powersetCard 2 := by
    intro B hB
    have hB' := mem_bases.mp hB
    have hcard : B.card = 2 := base_card hd hB'
    have hsmall := (small_indep M B (by omega)).mp hB'.indep
    rw [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro C hC
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
      refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
      change i ∈ Finset.univ.filter M.IsNonloop
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hsmall.1 i hi⟩
    · have hInj : Set.InjOn (parClass M) B := hsmall.2
      rw [Finset.card_image_of_injOn hInj, hcard]
  have hfiber : ∀ t ∈ (parClasses M).powersetCard 2,
      (bases M).filter (fun B => B.image (parClass M) = t) =
        (selections (nonloops M) (parClass M)).filter
          (fun B => B.image (parClass M) = t) := by
    intro t ht
    ext B
    simp only [Finset.mem_filter, mem_bases]
    constructor
    · intro ⟨hB, him⟩
      have hsmall := (small_indep M B (by rw [base_card hd hB])).mp hB.indep
      have hInj : Set.InjOn (parClass M) B := hsmall.2
      have hU' : ∀ i ∈ B, i ∈ nonloops M := fun i hi => by
        change i ∈ Finset.univ.filter M.IsNonloop
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hsmall.1 i hi⟩
      exact ⟨mem_selections.mpr ⟨hU', hInj⟩, him⟩
    · intro ⟨hsel, him⟩
      obtain ⟨hU, hI⟩ := mem_selections.mp hsel
      have hcard : B.card = 2 := by
        rw [← Finset.card_image_of_injOn hI, him]
        exact (Finset.mem_powersetCard.mp ht).2
      have hindep := (small_indep M B (by rw [hcard])).mpr ⟨fun i hi =>
        (Finset.mem_filter.mp (hU hi)).2, hI⟩
      have hbase : M.IsBase (B : Set (Fin n)) := by
        apply hindep.isBase_of_eRk_ge (Set.finite_univ.subset (Set.subset_univ _))
        rw [hd, hindep.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard, hcard]
        norm_num
      exact ⟨hbase, him⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro t ht
  rw [hfiber t ht]
  calc ∑ B ∈ (selections (nonloops M) (parClass M)).filter
        (fun B => B.image (parClass M) = t), ∏ i ∈ B, (z i : ℂ)
      = ∏ C ∈ t, ∑ i ∈ (nonloops M).filter (fun i => parClass M i = C), (z i : ℂ) :=
        (prod_fiber_sums (nonloops M) (parClass M) t (fun i => (z i : ℂ))).symm
    _ = ∏ C ∈ t, classSum M z C :=
        Finset.prod_congr rfl fun C _ => rfl

open scoped Polynomial in
/-- **Gauss–Lucas at the origin.** If all roots of a nonzero complex polynomial have
imaginary part at most `-δ < 0`, then no iterated derivative vanishes at `0`: by
Gauss–Lucas the roots of each derivative lie in the convex hull of the roots, which
stays in the same closed half-plane. -/
private lemma iterate_derivative_eval_zero_ne_zero {δ : ℝ} (hδ : 0 < δ) :
    ∀ (k : ℕ) (P : ℂ[X]), P ≠ 0 → k ≤ P.natDegree →
      P.rootSet ℂ ⊆ {w | w.im ≤ -δ} → (Polynomial.derivative^[k] P).eval 0 ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro P hP _ hroots
    rw [Function.iterate_zero_apply]
    intro he
    have h0 : (0 : ℂ) ∈ P.rootSet ℂ := by
      apply Polynomial.mem_rootSet.mpr ⟨hP, ?_⟩
      simpa using he
    have := hroots h0
    simp at this
    linarith
  | succ k ih =>
    intro P hP hk hroots
    rw [Function.iterate_succ_apply]
    have hdeg : 0 < P.degree := by
      rw [Polynomial.degree_eq_natDegree hP]
      exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hQ : Polynomial.derivative P ≠ 0 :=
      Polynomial.derivative_ne_zero.mpr (by omega)
    have hrootsQ : (Polynomial.derivative P).rootSet ℂ ⊆ {w | w.im ≤ -δ} := by
      intro w hw
      have hconv := Polynomial.rootSet_derivative_subset_convexHull_rootSet hdeg hw
      have hsub : (convexHull ℝ) (P.rootSet ℂ) ⊆ {w | w.im ≤ -δ} :=
        convexHull_min hroots (convex_halfSpace_le Complex.imLm.isLinear (-δ))
      exact hsub hconv
    exact ih (Polynomial.derivative P) hQ (by rw [Polynomial.natDegree_derivative]; omega)
      hrootsQ

/-- **Degree two.** The bases are the pairs of nonloops from distinct parallel classes,
so the value of the polynomial is the second elementary symmetric function of the
class sums. That coefficient of the product over the classes is nonzero by
Gauss–Lucas: the product's roots are the negatives of the class sums, whose
imaginary parts are uniformly negative. -/
private lemma stable_two {M : _root_.Matroid (Fin n)} (hd : M.eRank = 2) :
    IsStable (basisForm M) := by
  classical
  right
  intro z
  obtain ⟨B₀, hB₀⟩ := exists_finset_isBase M
  have hcard₀ : B₀.card = 2 := base_card hd hB₀
  obtain ⟨i, j, hij, hB₀eq⟩ := Finset.card_eq_two.mp hcard₀
  have hsmall₀ := (small_indep M B₀ (by rw [hcard₀])).mp hB₀.indep
  have hInj₀ : Set.InjOn (parClass M) B₀ := hsmall₀.2
  have hiB : i ∈ B₀ := by simp [hB₀eq]
  have hjB : j ∈ B₀ := by simp [hB₀eq]
  have hneij : parClass M i ≠ parClass M j := fun he => hij (hInj₀ hiB hjB he)
  have hnonloop : ∀ k ∈ B₀, k ∈ nonloops M := fun k hk => by
    change k ∈ Finset.univ.filter M.IsNonloop
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, hsmall₀.1 k hk⟩
  have hclasses : 2 ≤ (parClasses M).card := by
    have hsub : ({parClass M i, parClass M j} : Finset (Set (Fin n))) ⊆ parClasses M := by
      intro C hC
      simp only [Finset.mem_insert, Finset.mem_singleton] at hC
      rcases hC with rfl | rfl
      · exact Finset.mem_image.mpr ⟨i, hnonloop i hiB, rfl⟩
      · exact Finset.mem_image.mpr ⟨j, hnonloop j hjB, rfl⟩
    calc 2 = ({parClass M i, parClass M j} : Finset (Set (Fin n))).card := by
          simp [hneij]
      _ ≤ (parClasses M).card := Finset.card_le_card hsub
  have hneClasses : (parClasses M).Nonempty :=
    ⟨parClass M i, Finset.mem_image.mpr ⟨i, hnonloop i hiB, rfl⟩⟩
  have hneIm : ((parClasses M).image (fun C => (classSum M z C).im)).Nonempty :=
    Finset.Nonempty.image hneClasses _
  set δ := ((parClasses M).image (fun C => (classSum M z C).im)).min' hneIm with hδdef
  have hδpos : 0 < δ := by
    have hmem := Finset.min'_mem _ hneIm
    obtain ⟨C, hC, hEq⟩ := Finset.mem_image.mp hmem
    rw [hδdef, ← hEq]
    exact classSum_im_pos hC
  have hδle : ∀ C ∈ parClasses M, δ ≤ (classSum M z C).im := fun C hC =>
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨C, hC, rfl⟩)
  set k := (parClasses M).card - 2 with hkdef
  set P : ℂ[X] :=
    ∏ C ∈ parClasses M, (Polynomial.X + Polynomial.C (classSum M z C)) with hPdef
  have hPne : P ≠ 0 := by
    rw [hPdef]
    exact (Polynomial.monic_prod_of_monic _ _ (fun C _ =>
      Polynomial.monic_X_add_C (classSum M z C))).ne_zero
  have hdegP : P.natDegree = (parClasses M).card := by
    rw [hPdef, Polynomial.natDegree_prod_of_monic
      (h := fun C _ => Polynomial.monic_X_add_C (classSum M z C))]
    simp
  have hk_le : k ≤ P.natDegree := by
    rw [hkdef, hdegP]
    omega
  have hroots : P.rootSet ℂ ⊆ {w | w.im ≤ -δ} := by
    intro w hw
    have hw' : w ∈ {w : ℂ | w.im ≤ -δ} := by
      rw [Polynomial.mem_rootSet] at hw
      obtain ⟨-, hev⟩ := hw
      rw [hPdef] at hev
      have hev' : P.eval w = 0 := by
        have : (Polynomial.aeval w) P = 0 := hev
        simpa using this
      rw [hPdef, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hev'
      obtain ⟨C, hC, hCw⟩ := hev'
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at hCw
      have hwv : w = -classSum M z C := eq_neg_of_add_eq_zero_left hCw
      rw [hwv]
      have hneg : (-classSum M z C).im = -(classSum M z C).im := by simp
      change (-classSum M z C).im ≤ -δ
      rw [hneg]
      have := hδle C hC
      linarith
    exact hw'
  have hderiv := iterate_derivative_eval_zero_ne_zero hδpos k P hPne hk_le hroots
  have hcoeff : P.coeff k =
      ∑ t ∈ (parClasses M).powersetCard 2, ∏ C ∈ t, classSum M z C := by
    have hcard2 : (parClasses M).card - k = 2 := by
      rw [hkdef]
      omega
    rw [hPdef, Finset.prod_X_add_C_coeff _ _ (by rw [hkdef]; omega), hcard2]
  have hderiv0 : (Polynomial.derivative^[k] P).eval 0 = (k.factorial : ℂ) * P.coeff k := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
    simp [Nat.descFactorial_self]
  rw [eval_basisForm_two hd z, ← hcoeff]
  intro hzero
  apply hderiv
  rw [hderiv0, hzero]
  simp

/-- The basis generating polynomial of a matroid of rank `d` is Lorentzian, by
induction on `d`: in degrees at most two it is stable, and in higher degrees its
support is M-convex and every derivative is the basis generating polynomial of a
contraction, or zero. -/
private lemma basisForm_mem_L : ∀ (d : ℕ) (M : _root_.Matroid (Fin n)),
    M.eRank = d → ∀ (g : H n d), g.1 = basisForm M → g ∈ L n d
  | 0, M, hd, g, hg => ⟨hg ▸ stable_zero hd, hg ▸ coeff_basisForm_nonneg M⟩
  | 1, M, hd, g, hg => ⟨hg ▸ stable_one hd, hg ▸ coeff_basisForm_nonneg M⟩
  | 2, M, hd, g, hg => ⟨hg ▸ stable_two hd, hg ▸ coeff_basisForm_nonneg M⟩
  | d + 3, M, hd, g, hg => by
    refine ⟨⟨hg ▸ convex_basisForm M, hg ▸ coeff_basisForm_nonneg M⟩, ?_⟩
    intro i
    by_cases hi : M.IsNonloop i
    · apply basisForm_mem_L (d + 2) (M ／ {i}) (eRank_contract_eq hi hd) _
      change pderiv i g.1 = basisForm (M ／ {i})
      rw [hg, pderiv_basisForm_of_isNonloop _ _ hi]
    · apply zero_mem_L
      change pderiv i g.1 = 0
      rw [hg, pderiv_basisForm_of_not_isNonloop _ _ hi]

open scoped Classical in
/-- **Basis generating polynomials of matroids are Lorentzian** (Brändén and Huh, *Lorentzian
polynomials*, Ann. of Math. 192 (2020), Theorem 3.10, (8) ⇒ (4)). If `M` is a matroid on
`[n]` of rank `d`, then its basis generating polynomial `∑_{B base} ∏_{i ∈ B} w_i` lies in
`L n d`. (For a zero-one set the generating function `f_J = ∑_{α ∈ J} w^α / α!` of the paper is
this polynomial, since `α! = 1`.) -/
theorem basisGeneratingPolynomial_mem_L {n d : ℕ} (M : _root_.Matroid (Fin n))
    (hd : M.eRank = d) (g : H n d)
    (hg : g.1 = ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin n) => M.IsBase (B : Set (Fin n))),
      monomial (indicatorVec B) (1 : ℝ)) :
    g ∈ L n d := by
  classical
  apply basisForm_mem_L _ M hd g
  rw [hg]
  rfl

end MathlibExt.Combinatorics.LorentzianToolboxWanted
