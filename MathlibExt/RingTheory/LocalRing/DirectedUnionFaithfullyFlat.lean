/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`Theorems/Thm_Subring_exists_isLocalRing_isNoetherianRing_faithfullyFlat_
of_directed_of_flat_of_map_maximalIdeal_eq.lean`
and
`P2M/Sol/S_Subring_exists_isLocalRing_isNoetherianRing_faithfullyFlat_
of_directed_of_flat_of_map_maximalIdeal_eq.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Tactic.IntervalCases

@[expose] public section

set_option autoImplicit false

universe u v

namespace P2mTowerNoetherian

open MvPolynomial IsLocalRing

section Criterion

variable {A : Type*} [CommRing A]

private lemma eval_mem_span_pow_of_isHomogeneous {σ : Type*} (t : σ → A) {F : MvPolynomial σ A} {n :
    ℕ}
    (hF : F.IsHomogeneous n) : eval t F ∈ Ideal.span (Set.range t) ^ n :=
  (Ideal.mem_span_pow_iff_exists_isHomogeneous t _).2 ⟨F, hF, rfl⟩

private lemma eval_mem_pow_succ_of_map_eq_zero {σ : Type*} (t : σ → A) (𝔪 : Ideal A)
    (h𝔪 : Ideal.span (Set.range t) = 𝔪) {F : MvPolynomial σ A} {n : ℕ}
    (hF : F.IsHomogeneous n) (h0 : MvPolynomial.map (Ideal.Quotient.mk 𝔪) F = 0) :
    eval t F ∈ 𝔪 ^ (n + 1) := by
  rw [F.as_sum, map_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hc : F.coeff d ∈ 𝔪 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← MvPolynomial.coeff_map, h0]
    simp
  have hdeg : d.degree = n := by
    rw [Finsupp.degree_eq_weight_one]; exact hF (mem_support_iff.mp hd)
  have hmon : eval t (monomial d (1 : A)) ∈ 𝔪 ^ n := by
    rw [← h𝔪]
    exact eval_mem_span_pow_of_isHomogeneous t (isHomogeneous_monomial _ hdeg)
  have : monomial d (F.coeff d) = C (F.coeff d) * monomial d 1 := by
    rw [C_mul_monomial, mul_one]
  rw [this, map_mul, eval_C, pow_succ']
  exact Ideal.mul_mem_mul hc hmon

private lemma isHomogeneous_map {σ S : Type*} [CommRing S] (f : A →+* S) {F : MvPolynomial σ A} {n :
    ℕ}
    (hF : F.IsHomogeneous n) : (MvPolynomial.map f F).IsHomogeneous n := by
  intro d hd
  rw [coeff_map] at hd
  exact hF fun h => hd (by rw [h, map_zero])

private lemma exists_isHomogeneous_map_eq {σ : Type*} (𝔪 : Ideal A) {n : ℕ}
    (Q : MvPolynomial σ (A ⧸ 𝔪)) (hQ : Q.IsHomogeneous n) :
    ∃ P : MvPolynomial σ A, P.IsHomogeneous n ∧
      MvPolynomial.map (Ideal.Quotient.mk 𝔪) P = Q := by
  classical
  let s : A ⧸ 𝔪 → A := fun c => (Ideal.Quotient.mk_surjective c).choose
  have hs : ∀ c, Ideal.Quotient.mk 𝔪 (s c) = c := fun c =>
    (Ideal.Quotient.mk_surjective c).choose_spec
  refine ⟨∑ d ∈ Q.support, monomial d (s (Q.coeff d)), ?_, ?_⟩
  · exact IsHomogeneous.sum _ _ _ fun d hd => isHomogeneous_monomial _
      (by rw [Finsupp.degree_eq_weight_one]; exact hQ (mem_support_iff.mp hd))
  · rw [map_sum]
    simp_rw [map_monomial, hs]
    exact Q.support_sum_monomial_coeff

section graded

variable {R σ : Type*} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma coe_decompose_eq_homogeneousComponent (φ : MvPolynomial σ R) (n : ℕ) :
    ((DirectSum.decompose (homogeneousSubmodule σ R) φ n : homogeneousSubmodule σ R n) :
      MvPolynomial σ R) = homogeneousComponent n φ :=
  decomposition.decompose'_apply φ n

private lemma homogeneousComponent_mul_left {c : MvPolynomial σ R} {i : ℕ} (hc : c.IsHomogeneous i)
    (Q : MvPolynomial σ R) (n : ℕ) :
    homogeneousComponent n (c * Q) =
      if i ≤ n then c * homogeneousComponent (n - i) Q else 0 := by
  classical
  have h := DirectSum.coe_decompose_mul_of_left_mem (𝒜 := homogeneousSubmodule σ R) (b := Q) n
    (show c ∈ homogeneousSubmodule σ R i from hc)
  rwa [coe_decompose_eq_homogeneousComponent, coe_decompose_eq_homogeneousComponent] at h

private lemma homogeneousComponent_mul_right (c : MvPolynomial σ R) {F : MvPolynomial σ R} {d : ℕ}
    (hF : F.IsHomogeneous d) (n : ℕ) :
    homogeneousComponent n (c * F) =
      if d ≤ n then homogeneousComponent (n - d) c * F else 0 := by
  classical
  have h := DirectSum.coe_decompose_mul_of_right_mem (𝒜 := homogeneousSubmodule σ R) (a := c) n
    (show F ∈ homogeneousSubmodule σ R d from hF)
  rwa [coe_decompose_eq_homogeneousComponent, coe_decompose_eq_homogeneousComponent] at h

end graded

variable (𝔪 : Ideal A) {σ : Type*} (t : σ → A) (I : Ideal A)

private def InitProp (Q : MvPolynomial σ (A ⧸ 𝔪)) : Prop :=
  ∀ n : ℕ, ∃ P : MvPolynomial σ A, P.IsHomogeneous n ∧
    MvPolynomial.map (Ideal.Quotient.mk 𝔪) P = homogeneousComponent n Q ∧
      eval t P ∈ I ⊔ 𝔪 ^ (n + 1)

variable {𝔪 t I}

private lemma InitProp.zero : InitProp 𝔪 t I 0 := fun n =>
  ⟨0, isHomogeneous_zero _ _ _, by simp, by simp⟩

private lemma InitProp.add {Q₁ Q₂ : MvPolynomial σ (A ⧸ 𝔪)} (h₁ : InitProp 𝔪 t I Q₁)
    (h₂ : InitProp 𝔪 t I Q₂) : InitProp 𝔪 t I (Q₁ + Q₂) := by
  intro n
  obtain ⟨P₁, hP₁, hm₁, he₁⟩ := h₁ n
  obtain ⟨P₂, hP₂, hm₂, he₂⟩ := h₂ n
  exact ⟨P₁ + P₂, hP₁.add hP₂, by rw [map_add, map_add, hm₁, hm₂],
    by rw [map_add]; exact Submodule.add_mem _ he₁ he₂⟩

private lemma InitProp.mul_of_isHomogeneous (h𝔪 : Ideal.span (Set.range t) = 𝔪)
    {c : MvPolynomial σ (A ⧸ 𝔪)} {i : ℕ} (hc : c.IsHomogeneous i)
    {Q : MvPolynomial σ (A ⧸ 𝔪)} (hQ : InitProp 𝔪 t I Q) : InitProp 𝔪 t I (c * Q) := by
  intro n
  rw [homogeneousComponent_mul_left hc]
  split_ifs with hin
  · obtain ⟨C', hC'h, hC'map⟩ := exists_isHomogeneous_map_eq 𝔪 c hc
    obtain ⟨P, hPh, hPmap, hPev⟩ := hQ (n - i)
    refine ⟨C' * P, ?_, ?_, ?_⟩
    · have := hC'h.mul hPh
      rwa [Nat.add_sub_cancel' hin] at this
    · rw [map_mul, hC'map, hPmap]
    · rw [map_mul]
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hPev
      rw [← hyz, mul_add]
      refine Submodule.add_mem_sup (Ideal.mul_mem_left _ _ hy) ?_
      have hC'ev : eval t C' ∈ 𝔪 ^ i := by
        rw [← h𝔪]; exact eval_mem_span_pow_of_isHomogeneous t hC'h
      have := Ideal.mul_mem_mul hC'ev hz
      rw [← pow_add] at this
      convert this using 2
      omega
  · exact ⟨0, isHomogeneous_zero _ _ _, by simp, by simp⟩

private lemma InitProp.mul (h𝔪 : Ideal.span (Set.range t) = 𝔪) (c : MvPolynomial σ (A ⧸ 𝔪))
    {Q : MvPolynomial σ (A ⧸ 𝔪)} (hQ : InitProp 𝔪 t I Q) : InitProp 𝔪 t I (c * Q) := by
  rw [← sum_homogeneousComponent c, Finset.sum_mul]
  exact Finset.sum_induction _ (InitProp 𝔪 t I) (fun _ _ => InitProp.add) InitProp.zero
    fun n _ => InitProp.mul_of_isHomogeneous h𝔪 (homogeneousComponent_isHomogeneous n c) hQ

variable (𝔪 t I) in
private def initIdeal (h𝔪 : Ideal.span (Set.range t) = 𝔪) : Ideal (MvPolynomial σ (A ⧸ 𝔪)) where
  carrier := {Q | InitProp 𝔪 t I Q}
  add_mem' := InitProp.add
  zero_mem' := InitProp.zero
  smul_mem' c _ hQ := InitProp.mul h𝔪 c hQ

private lemma mem_initIdeal_iff (h𝔪 : Ideal.span (Set.range t) = 𝔪) (Q : MvPolynomial σ (A ⧸ 𝔪)) :
    Q ∈ initIdeal 𝔪 t I h𝔪 ↔ InitProp 𝔪 t I Q := Iff.rfl

private lemma map_mem_initIdeal (h𝔪 : Ideal.span (Set.range t) = 𝔪) {G : MvPolynomial σ A} {m : ℕ}
    (hG : G.IsHomogeneous m) (hev : eval t G ∈ I ⊔ 𝔪 ^ (m + 1)) :
    MvPolynomial.map (Ideal.Quotient.mk 𝔪) G ∈ initIdeal 𝔪 t I h𝔪 := by
  intro n
  rw [homogeneousComponent_of_mem
    (show MvPolynomial.map (Ideal.Quotient.mk 𝔪) G ∈ homogeneousSubmodule σ (A ⧸ 𝔪) m from
      isHomogeneous_map _ hG)]
  by_cases hnm : n = m
  · subst hnm
    exact ⟨G, hG, by rw [ite_eq_left rfl], hev⟩
  · exact ⟨0, isHomogeneous_zero _ _ _, by rw [ite_eq_right hnm, map_zero], by simp⟩

private lemma homogeneousComponent_mem_initIdeal (h𝔪 : Ideal.span (Set.range t) = 𝔪)
    {Q : MvPolynomial σ (A ⧸ 𝔪)} (hQ : Q ∈ initIdeal 𝔪 t I h𝔪) (m : ℕ) :
    homogeneousComponent m Q ∈ initIdeal 𝔪 t I h𝔪 := by
  intro n
  rw [homogeneousComponent_of_mem (homogeneousComponent_mem m Q)]
  by_cases hnm : n = m
  · subst hnm
    rw [ite_eq_left rfl]
    exact hQ n
  · exact ⟨0, isHomogeneous_zero _ _ _, by rw [ite_eq_right hnm, map_zero], by simp⟩

private theorem exists_fg_le_and_forall_le_sup_pow (𝔪 : Ideal A) (h𝔪 : 𝔪.FG)
    [IsNoetherianRing (A ⧸ 𝔪)] (I : Ideal A) :
    ∃ J : Ideal A, J ≤ I ∧ J.FG ∧ ∀ m : ℕ, I ≤ J ⊔ 𝔪 ^ m := by
  classical
  obtain ⟨s, hs⟩ := h𝔪

  let t : s → A := fun x => (x : A)
  have h𝔪t : Ideal.span (Set.range t) = 𝔪 := by
    rw [← hs]
    congr 1
    ext a
    simp only [t, Set.mem_range, Subtype.exists, exists_prop, exists_eq_right, Finset.mem_coe]
  set π : A →+* A ⧸ 𝔪 := Ideal.Quotient.mk 𝔪 with hπ
  let Ish : Ideal (MvPolynomial s (A ⧸ 𝔪)) := initIdeal 𝔪 t I h𝔪t
  obtain ⟨S₀, hS₀⟩ := IsNoetherian.noetherian Ish
  let D : ℕ := S₀.sup totalDegree
  let T : Finset (MvPolynomial s (A ⧸ 𝔪) × ℕ) := S₀ ×ˢ Finset.range (D + 1)
  let Fb : MvPolynomial s (A ⧸ 𝔪) × ℕ → MvPolynomial s (A ⧸ 𝔪) :=
    fun p => homogeneousComponent p.2 p.1
  have hFb_hom : ∀ p, (Fb p).IsHomogeneous p.2 := fun p =>
    homogeneousComponent_isHomogeneous _ _
  have hFb_mem : ∀ p ∈ T, Fb p ∈ Ish := by
    intro p hp
    have hp1 : p.1 ∈ Ish := by
      rw [← hS₀]
      exact Ideal.subset_span (Finset.mem_product.mp hp).1
    exact homogeneousComponent_mem_initIdeal h𝔪t hp1 p.2

  have hIsh_le : Ish ≤ Ideal.span (Fb '' ↑T) := by
    rw [← hS₀, Ideal.span_le]
    intro Q hQ
    have hQeq : Q = ∑ n ∈ Finset.range (Q.totalDegree + 1), homogeneousComponent n Q :=
      (sum_homogeneousComponent Q).symm
    rw [SetLike.mem_coe, hQeq]
    refine Ideal.sum_mem _ fun n hn => Ideal.subset_span ⟨(Q, n), ?_, rfl⟩
    rw [Finset.mem_coe, Finset.mem_product]
    refine ⟨hQ, Finset.mem_range.mpr ?_⟩
    have h1 : Q.totalDegree ≤ D := Finset.le_sup (f := totalDegree) hQ
    have h2 := Finset.mem_range.mp hn
    omega

  have hgen : ∀ p ∈ T, ∃ F : MvPolynomial s A, ∃ y m' : A, F.IsHomogeneous p.2 ∧
      MvPolynomial.map π F = Fb p ∧ y ∈ I ∧ m' ∈ 𝔪 ^ (p.2 + 1) ∧ eval t F = y + m' := by
    intro p hp
    obtain ⟨F, hFh, hFmap, hFev⟩ := hFb_mem p hp p.2
    rw [homogeneousComponent_of_mem (hFb_hom p), ite_eq_left rfl] at hFmap
    obtain ⟨y, hy, m', hm', h⟩ := Submodule.mem_sup.mp hFev
    exact ⟨F, y, m', hFh, hFmap, hy, hm', h.symm⟩
  choose! F y m' hFh hFmap hyI hm'𝔪 hFev using hgen
  let J : Ideal A := Ideal.span (y '' ↑T)
  have hJI : J ≤ I := Ideal.span_le.mpr (by rintro _ ⟨p, hp, rfl⟩; exact hyI p hp)
  have hJfg : J.FG := ⟨T.image y, by simp [J, Finset.coe_image]⟩
  refine ⟨J, hJI, hJfg, fun m => ?_⟩
  induction m with
  | zero => simp
  | succ m ih =>
    intro z hz
    obtain ⟨j, hj, w, hw, hjw⟩ := Submodule.mem_sup.mp (ih hz)
    have hwI : w ∈ I := by
      have := I.sub_mem hz (hJI hj)
      rwa [← hjw, add_sub_cancel_left] at this
    rw [← h𝔪t] at hw
    obtain ⟨G, hGh, hGw⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous t w).mp hw
    have hGb : MvPolynomial.map π G ∈ Ish :=
      map_mem_initIdeal h𝔪t hGh (by rw [hGw]; exact Submodule.mem_sup_left hwI)
    obtain ⟨l, hl, hlG⟩ :=
      (Finsupp.mem_span_image_iff_linearCombination _).mp (hIsh_le hGb)
    rw [Finsupp.linearCombination_apply_of_mem_supported _ hl] at hlG

    have hcomp : MvPolynomial.map π G =
        ∑ p ∈ T with p.2 ≤ m, homogeneousComponent (m - p.2) (l p) * Fb p := by
      have h1 : homogeneousComponent m (MvPolynomial.map π G) = MvPolynomial.map π G := by
        rw [homogeneousComponent_of_mem (show MvPolynomial.map π G ∈
          homogeneousSubmodule s (A ⧸ 𝔪) m from isHomogeneous_map _ hGh), ite_eq_left rfl]
      rw [← h1, ← hlG, map_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [smul_eq_mul, homogeneousComponent_mul_right _ (hFb_hom p)]

    have hH : ∀ p : MvPolynomial s (A ⧸ 𝔪) × ℕ, ∃ H : MvPolynomial s A,
        H.IsHomogeneous (m - p.2) ∧
          MvPolynomial.map π H = homogeneousComponent (m - p.2) (l p) := fun p =>
      exists_isHomogeneous_map_eq 𝔪 _ (homogeneousComponent_isHomogeneous _ _)
    choose H hHh hHmap using hH
    set G' : MvPolynomial s A := G - ∑ p ∈ T with p.2 ≤ m, H p * F p with hG'
    have hG'h : G'.IsHomogeneous m := by
      refine hGh.sub (IsHomogeneous.sum _ _ _ fun p hp => ?_)
      obtain ⟨hpT, hp2⟩ := Finset.mem_filter.mp hp
      have := (hHh p).mul (hFh p hpT)
      rwa [Nat.sub_add_cancel hp2] at this
    have hG'map : MvPolynomial.map π G' = 0 := by
      rw [hG', map_sub, map_sum, hcomp, sub_eq_zero]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [map_mul, hHmap, hFmap p (Finset.mem_filter.mp hp).1]
    have hG'ev : eval t G' ∈ 𝔪 ^ (m + 1) :=
      eval_mem_pow_succ_of_map_eq_zero t 𝔪 h𝔪t hG'h hG'map
    have hsum : eval t (∑ p ∈ T with p.2 ≤ m, H p * F p) ∈ J ⊔ 𝔪 ^ (m + 1) := by
      rw [map_sum]
      refine Submodule.sum_mem _ fun p hp => ?_
      obtain ⟨hpT, hp2⟩ := Finset.mem_filter.mp hp
      rw [map_mul, hFev p hpT, mul_add]
      refine Submodule.add_mem_sup
        (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨p, hpT, rfl⟩)) ?_
      have hHev : eval t (H p) ∈ 𝔪 ^ (m - p.2) := by
        have := eval_mem_span_pow_of_isHomogeneous t (hHh p)
        rwa [h𝔪t] at this
      have := Ideal.mul_mem_mul hHev (hm'𝔪 p hpT)
      rw [← pow_add] at this
      convert this using 2
      omega
    have hwmem : w ∈ J ⊔ 𝔪 ^ (m + 1) := by
      have : w = eval t G' + eval t (∑ p ∈ T with p.2 ≤ m, H p * F p) := by
        rw [hG', map_sub, sub_add_cancel, hGw]
      rw [this]
      exact Submodule.add_mem _ (Submodule.mem_sup_right hG'ev) hsum
    rw [← hjw]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hj) hwmem

private theorem isNoetherianRing_of_fg_of_forall_fg_iInf_sup_pow_le (𝔪 : Ideal A) (h𝔪 : 𝔪.FG)
    [IsNoetherianRing (A ⧸ 𝔪)]
    (hclosed : ∀ J : Ideal A, J.FG → ⨅ n : ℕ, J ⊔ 𝔪 ^ n ≤ J) : IsNoetherianRing A := by
  rw [isNoetherianRing_iff, isNoetherian_def]
  intro I
  obtain ⟨J, hJI, hJfg, hIJ⟩ := exists_fg_le_and_forall_le_sup_pow 𝔪 h𝔪 I
  have : I = J := le_antisymm ((le_iInf hIJ).trans (hclosed J hJfg)) hJI
  rw [this]
  exact hJfg

end Criterion

section FlatUnion

open TensorProduct

private theorem flat_of_directed_of_forall_flat {R M : Type*} [CommRing R] [AddCommGroup M] [Module
    R M]
    {κ : Type*} [Nonempty κ] (T : κ → Submodule R M)
    (hdir : ∀ a b, ∃ c, T a ≤ T c ∧ T b ≤ T c) (hcov : ∀ x, ∃ a, x ∈ T a)
    (hT : ∀ a, Module.Flat R (T a)) : Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I hI
  rw [injective_iff_map_eq_zero]
  intro u hu

  have key : ∀ u : I ⊗[R] M, ∃ a, ∃ v : I ⊗[R] (T a),
      LinearMap.lTensor I (T a).subtype v = u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨Classical.arbitrary κ, 0, map_zero _⟩
    | tmul x m =>
      obtain ⟨a, ha⟩ := hcov m
      exact ⟨a, x ⊗ₜ ⟨m, ha⟩, by simp⟩
    | add u₁ u₂ h₁ h₂ =>
      obtain ⟨a₁, v₁, rfl⟩ := h₁
      obtain ⟨a₂, v₂, rfl⟩ := h₂
      obtain ⟨c, h₁c, h₂c⟩ := hdir a₁ a₂
      refine ⟨c, LinearMap.lTensor I (Submodule.inclusion h₁c) v₁ +
        LinearMap.lTensor I (Submodule.inclusion h₂c) v₂, ?_⟩
      rw [map_add, ← LinearMap.comp_apply (f := LinearMap.lTensor I (T c).subtype),
        ← LinearMap.lTensor_comp, ← LinearMap.comp_apply (f := LinearMap.lTensor I (T c).subtype),
        ← LinearMap.lTensor_comp, Submodule.subtype_comp_inclusion,
        Submodule.subtype_comp_inclusion]
  obtain ⟨a, v, rfl⟩ := key u
  have hnat : ∀ v : I ⊗[R] (T a),
      TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype) (LinearMap.lTensor I (T a).subtype
          v)
        = (T a).subtype (TensorProduct.lift ((LinearMap.lsmul R (T a)).comp I.subtype) v) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add v₁ v₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  rw [hnat] at hu
  have hv : TensorProduct.lift ((LinearMap.lsmul R (T a)).comp I.subtype) v = 0 :=
    (T a).injective_subtype (by rw [hu, map_zero])
  have hinj := (Module.Flat.iff_lift_lsmul_comp_subtype_injective.mp (hT a)) hI
  rw [(injective_iff_map_eq_zero _).mp hinj v hv, map_zero]

end FlatUnion

section Tower

variable {A : Type*} [CommRing A] {ι : Type*} [Preorder ι]
  (S : ι → Subring A) (hS : Monotone S)

private def towerSubmodule {i j : ι} (h : i ≤ j) : Submodule (S i) A where
  carrier := S j
  add_mem' := (S j).add_mem
  zero_mem' := (S j).zero_mem
  smul_mem' r _ ha := (S j).mul_mem (hS h r.2) ha

private lemma mem_towerSubmodule {i j : ι} (h : i ≤ j) (x : A) :
    x ∈ towerSubmodule S hS h ↔ x ∈ S j := Iff.rfl

private lemma flat_towerSubmodule {i j : ι} (h : i ≤ j) (hflat : (Subring.inclusion (hS h)).Flat) :
    Module.Flat (S i) (towerSubmodule S hS h) := by
  letI : Algebra (S i) (S j) := (Subring.inclusion (hS h)).toAlgebra
  haveI : Module.Flat (S i) (S j) := hflat
  let e : towerSubmodule S hS h ≃ₗ[S i] S j :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Flat.of_linearEquiv e

private theorem flat_of_tower [IsDirected ι (· ≤ ·)] (hcov : ∀ x : A, ∃ i, x ∈ S i)
    (hflat : ∀ ⦃i j : ι⦄ (h : i ≤ j), (Subring.inclusion (hS h)).Flat) (i : ι) :
    Module.Flat (S i) A := by
  haveI : Nonempty {j // i ≤ j} := ⟨⟨i, le_rfl⟩⟩
  refine flat_of_directed_of_forall_flat (κ := {j // i ≤ j})
    (fun j => towerSubmodule S hS j.2) ?_ ?_ ?_
  · rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a b
    exact ⟨⟨c, ha.trans hac⟩, fun x hx => hS hac hx, fun x hx => hS hbc hx⟩
  · intro x
    obtain ⟨l, hl⟩ := hcov x
    obtain ⟨c, hic, hlc⟩ := directed_of (· ≤ ·) i l
    exact ⟨⟨c, hic⟩, hS hlc hl⟩
  · intro j
    exact flat_towerSubmodule S hS j.2 (hflat j.2)

variable [∀ i, IsLocalRing (S i)]

private lemma isUnit_coe_iff [IsDirected ι (· ≤ ·)] (hcov : ∀ x : A, ∃ i, x ∈ S i)
    (hle : ∀ ⦃i j : ι⦄ (h : i ≤ j),
      Ideal.map (Subring.inclusion (hS h)) (maximalIdeal (S i)) ≤ maximalIdeal (S j))
    {j : ι} (x : S j) : IsUnit (x : A) ↔ IsUnit x := by
  refine ⟨fun hx => ?_, fun hx => hx.map (S j).subtype⟩
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨l, hl⟩ := hcov y
  obtain ⟨u, hju, hlu⟩ := directed_of (· ≤ ·) j l
  by_contra hxu
  have hxm : Subring.inclusion (hS hju) x ∈ maximalIdeal (S u) :=
    hle hju (Ideal.mem_map_of_mem _ hxu)
  exact hxm (IsUnit.of_mul_eq_one ⟨y, hS hlu hl⟩ (Subtype.ext hy))

omit [Preorder ι] in

private lemma isLocalRing [Nonempty ι] (S : ι → Subring A) [∀ i, IsLocalRing (S i)]
    (hcov : ∀ x : A, ∃ i, x ∈ S i) : IsLocalRing A := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  haveI : Nontrivial A := ⟨⟨0, 1, fun h => zero_ne_one ((Subtype.ext h : (0 : S i₀) = 1))⟩⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  obtain ⟨j, hj⟩ := hcov a
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨a, hj⟩ : S j) with h | h
  · exact Or.inl (h.map (S j).subtype)
  · exact Or.inr (by simpa using h.map (S j).subtype)

private lemma map_maximalIdeal_eq [IsDirected ι (· ≤ ·)] (hcov : ∀ x : A, ∃ i, x ∈ S i) [IsLocalRing
    A]
    (hmax : ∀ ⦃i j : ι⦄ (h : i ≤ j),
      Ideal.map (Subring.inclusion (hS h)) (maximalIdeal (S i)) = maximalIdeal (S j)) (i : ι) :
    Ideal.map (algebraMap (S i) A) (maximalIdeal (S i)) = maximalIdeal A := by
  have hle : ∀ ⦃i j : ι⦄ (h : i ≤ j),
      Ideal.map (Subring.inclusion (hS h)) (maximalIdeal (S i)) ≤ maximalIdeal (S j) :=
    fun i j h => (hmax h).le
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => hx ((isUnit_coe_iff S hS hcov hle x).mp h)
  · intro a ha
    obtain ⟨j₀, hj₀⟩ := hcov a
    obtain ⟨j, hij, hj₀j⟩ := directed_of (· ≤ ·) i j₀
    have haj : a ∈ S j := hS hj₀j hj₀
    have hunit : ¬ IsUnit (⟨a, haj⟩ : S j) := fun h =>
      ha ((isUnit_coe_iff S hS hcov hle ⟨a, haj⟩).mpr h)
    have hmem : (⟨a, haj⟩ : S j) ∈ Ideal.map (Subring.inclusion (hS hij)) (maximalIdeal (S i)) := by
      rw [hmax hij]; exact hunit
    have : Ideal.map (algebraMap (S i) A) (maximalIdeal (S i)) =
        Ideal.map (algebraMap (S j) A)
          (Ideal.map (Subring.inclusion (hS hij)) (maximalIdeal (S i))) := by
      rw [Ideal.map_map]; rfl
    rw [this]
    exact Ideal.mem_map_of_mem (algebraMap (S j) A) hmem

private lemma iInf_sup_pow_le [Nonempty ι] [IsDirected ι (· ≤ ·)] (hcov : ∀ x : A, ∃ i, x ∈ S i)
    [IsLocalRing A] [∀ i, IsNoetherianRing (S i)]
    (hflat : ∀ ⦃i j : ι⦄ (h : i ≤ j), (Subring.inclusion (hS h)).Flat)
    (hmax : ∀ ⦃i j : ι⦄ (h : i ≤ j),
      Ideal.map (Subring.inclusion (hS h)) (maximalIdeal (S i)) = maximalIdeal (S j))
    (J : Ideal A) (hJ : J.FG) : ⨅ n : ℕ, J ⊔ maximalIdeal A ^ n ≤ J := by
  classical
  intro x hx
  obtain ⟨g, hg⟩ := hJ
  have hcov' : ∀ x : A, ∃ i, x ∈ S i := hcov
  choose idx hidx using hcov'
  obtain ⟨j, hj⟩ := Finset.exists_le (insert (idx x) (g.image idx))
  have hxj : x ∈ S j := hS (hj _ (Finset.mem_insert_self _ _)) (hidx x)
  have hgj : ∀ a ∈ g, a ∈ S j := fun a ha =>
    hS (hj _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem idx ha))) (hidx a)

  let Jj : Ideal (S j) := Ideal.span ((S j).subtype ⁻¹' (g : Set A))
  have hJmap : Jj.map (algebraMap (S j) A) = J := by
    rw [Ideal.map_span, ← hg]
    congr 1
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩; exact hb
    · intro ha; exact ⟨⟨a, hgj a ha⟩, ha, rfl⟩
  have hmmap := map_maximalIdeal_eq S hS hcov hmax j
  haveI : Module.Flat (S j) A := flat_of_tower S hS hcov hflat j
  haveI : IsLocalHom (algebraMap (S j) A) :=
    ⟨fun y hy => (isUnit_coe_iff S hS hcov (fun i j h => (hmax h).le) y).mp hy⟩
  haveI : Module.FaithfullyFlat (S j) A := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hxmem : ∀ n : ℕ, (⟨x, hxj⟩ : S j) ∈ Jj ⊔ maximalIdeal (S j) ^ n := by
    intro n
    have h1 : x ∈ J ⊔ maximalIdeal A ^ n := (Submodule.mem_iInf _).mp hx n
    rw [← hJmap, ← hmmap, ← Ideal.map_pow, ← Ideal.map_sup] at h1
    have h2 : (⟨x, hxj⟩ : S j) ∈
        (Ideal.map (algebraMap (S j) A) (Jj ⊔ maximalIdeal (S j) ^ n)).comap
          (algebraMap (S j) A) := h1
    rwa [Ideal.comap_map_eq_self_of_faithfullyFlat] at h2

  have hxJj : (⟨x, hxj⟩ : S j) ∈ Jj := by
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := S j) (M := S j ⧸ Jj)
      (I := maximalIdeal (S j)) (maximalIdeal.isMaximal (S j)).ne_top
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Submodule.mem_bot (R := S j), ← hK,
      Submodule.mem_iInf]
    intro n
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hxmem n)
    rw [← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
    have : Ideal.Quotient.mk Jj b = b • Ideal.Quotient.mk Jj 1 := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_one, mul_one]
    rw [this]
    exact Submodule.smul_mem_smul hb Submodule.mem_top
  have : x = algebraMap (S j) A ⟨x, hxj⟩ := rfl
  rw [this, ← hJmap]
  exact Ideal.mem_map_of_mem _ hxJj

private theorem main [Nonempty ι] [IsDirected ι (· ≤ ·)] (hcov : ∀ x : A, ∃ i, x ∈ S i)
    [∀ i, IsNoetherianRing (S i)]
    (hflat : ∀ ⦃i j : ι⦄ (h : i ≤ j), (Subring.inclusion (hS h)).Flat)
    (hmax : ∀ ⦃i j : ι⦄ (h : i ≤ j),
      Ideal.map (Subring.inclusion (hS h)) (maximalIdeal (S i)) = maximalIdeal (S j)) :
    ∃ _ : IsLocalRing A, IsNoetherianRing A ∧
      ∀ i, Module.FaithfullyFlat (S i) A ∧
        Ideal.map (algebraMap (S i) A) (maximalIdeal (S i)) = maximalIdeal A := by
  haveI hloc : IsLocalRing A := isLocalRing S hcov
  have hle : ∀ ⦃i j : ι⦄ (h : i ≤ j),
      Ideal.map (Subring.inclusion (hS h)) (maximalIdeal (S i)) ≤ maximalIdeal (S j) :=
    fun i j h => (hmax h).le
  have hff : ∀ i, Module.FaithfullyFlat (S i) A := by
    intro i
    haveI : Module.Flat (S i) A := flat_of_tower S hS hcov hflat i
    haveI : IsLocalHom (algebraMap (S i) A) :=
      ⟨fun y hy => (isUnit_coe_iff S hS hcov hle y).mp hy⟩
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine ⟨hloc, ?_, fun i => ⟨hff i, map_maximalIdeal_eq S hS hcov hmax i⟩⟩
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hfg : (maximalIdeal A).FG := by
    rw [← map_maximalIdeal_eq S hS hcov hmax i₀]
    exact Ideal.FG.map (IsNoetherian.noetherian (maximalIdeal (S i₀))) (algebraMap (S i₀) A)
  haveI : IsNoetherianRing (A ⧸ maximalIdeal A) :=
    inferInstanceAs (IsNoetherianRing (ResidueField A))
  exact isNoetherianRing_of_fg_of_forall_fg_iInf_sup_pow_le (maximalIdeal A) hfg
    (iInf_sup_pow_le S hS hcov hflat hmax)

end Tower

end P2mTowerNoetherian

/-- A directed union of Noetherian local subrings, with flat inclusion maps
between comparable stages and with the maximal ideal of each stage mapping
exactly onto the maximal ideal of any larger stage, is itself Noetherian
and local, and is faithfully flat over every stage, with each stage maximal
ideal extending to the maximal ideal of the union. -/
public theorem
    Subring.exists_isLocalRing_isNoetherianRing_faithfullyFlat_of_directed_of_flat_of_map_maximalIdeal_eq
    (A : Type u) [CommRing A] {ι : Type v} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (S : ι → Subring A) (hS : Monotone S) (hcov : ∀ x : A, ∃ i, x ∈ S i)
    [∀ i, IsLocalRing (S i)] [∀ i, IsNoetherianRing (S i)]
    (hflat : ∀ ⦃i j : ι⦄ (h : i ≤ j), (Subring.inclusion (hS h)).Flat)
    (hmax : ∀ ⦃i j : ι⦄ (h : i ≤ j),
      Ideal.map (Subring.inclusion (hS h)) (IsLocalRing.maximalIdeal (S i)) =
        IsLocalRing.maximalIdeal (S j)) :
    ∃ _ : IsLocalRing A, IsNoetherianRing A ∧
      ∀ i, Module.FaithfullyFlat (S i) A ∧
        Ideal.map (algebraMap (S i) A) (IsLocalRing.maximalIdeal (S i)) =
          IsLocalRing.maximalIdeal A :=
  P2mTowerNoetherian.main S hS hcov hflat hmax
