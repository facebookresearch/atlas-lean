/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import MathlibExt.Algebra.Homology.FirstQuadrantSpectralSequenceData

/-!
# Boundary support for the horizontal first-quadrant spectral sequence

Let K be a nonnegative homological bicomplex in an abelian category C.
Its complete horizontal filtration F_a is zero for finite a<0 and
contains all total-degree t terms once 0≤a and t≤a.toNat.
After reindexing total chain degree t as cochain degree −t, the
interval maps F_i → F_j are monic. If such a map is epic in degree n,
its relative cochain homology H^n(Cone(F_i → F_j)) is zero.

For page r≥1 the differential has bidegree (−r,r−1). Absence of an
outgoing bidegree implies p<r, so both stages p−r−1 and p−r are zero.
Absence of an incoming bidegree implies q<r−1, so the upper interval
map from p+r−1 to p+r is invertible in total degree p+q+1.
These are the two boundary-support vanishings required for the
spectral sequence starting at the relative-homology first page.
The category object and morphism worlds are independent.
-/

@[expose] public section

open CategoryTheory Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

noncomputable instance horizontalCompleteFilteredTotalMap_mono
    {i j : EInt} (h : i ≤ j) :
    Mono (horizontalCompleteFilteredTotalMap K h) :=
  mono_of_mono_fac (horizontalCompleteFilteredTotalMap_toTotal K h)

/-- For a nonnegative homological bicomplex K in an abelian
category, a∈ℤ with a≥0 and t∈ℕ with t≤a.toNat, the stage inclusion
F_a → Tot(K) is an isomorphism in degree t.
Every total bidegree in that degree has horizontal coordinate at most a. -/
theorem horizontalCompleteFilteredTotalToTotal_f_isIso_of_nonneg
    (a : ℤ) (ha : 0 ≤ a) (t : ℕ) (ht : t ≤ a.toNat) :
    IsIso ((horizontalCompleteFilteredTotalToTotal K (a : EInt)).f t) := by
  change IsIso (((if 0 ≤ a then
      (horizontalTotalFiltration K).toMonoOver.obj a.toNat
    else horizontalCompleteFilteredTotalZeroMonoOver K).arrow).f t)
  rw [ite_eq_left ha]
  change IsIso ((horizontalFilteredTotalComplexToTotal K a.toNat).f t)
  exact (horizontalFilteredTotalIsoOfLE K a.toNat t ht).isIso_hom

/-- For a nonnegative homological bicomplex K in an abelian
category, i≤j in EInt and t∈ℕ, if both degree-t inclusions
F_i → Tot(K) and F_j → Tot(K) are isomorphisms, then the
degree-t transition F_i → F_j is an isomorphism.
The transition commutes with the two total inclusions. -/
theorem horizontalCompleteFilteredTotalMap_f_isIso_of_toTotal
    {i j : EInt} (h : i ≤ j) (t : ℕ)
    [hi : IsIso ((horizontalCompleteFilteredTotalToTotal K i).f t)]
    [hj : IsIso ((horizontalCompleteFilteredTotalToTotal K j).f t)] :
    IsIso ((horizontalCompleteFilteredTotalMap K h).f t) := by
  have hcomp : IsIso ((horizontalCompleteFilteredTotalMap K h).f t ≫
      (horizontalCompleteFilteredTotalToTotal K j).f t) := by
    rw [← HomologicalComplex.comp_f,
      horizontalCompleteFilteredTotalMap_toTotal]
    infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    ((horizontalCompleteFilteredTotalMap K h).f t)
    ((horizontalCompleteFilteredTotalToTotal K j).f t) hj hcomp

/-- For a nonnegative homological bicomplex K in an abelian
category, if the degree-t component of F_i → F_j is an
isomorphism, then its extended cochain component in degree −t
is an isomorphism. Here i≤j in EInt and t∈ℕ. -/
theorem horizontalCompleteFiltrationCochainDiagram_map_f_isIso
    {i j : EInt} (h : i ≤ j) (t : ℕ)
    [hmap : IsIso ((horizontalCompleteFilteredTotalMap K h).f t)] :
    IsIso (((horizontalCompleteFiltrationCochainDiagram K).map
      (homOfLE h)).f (-(t : ℤ))) := by
  change IsIso ((HomologicalComplex.extendMap
    (horizontalCompleteFilteredTotalMap K h)
      ComplexShape.embeddingDownNat).f (-(t : ℤ)))
  rw [HomologicalComplex.extendMap_f _ _
    (i := t) (i' := -(t : ℤ)) (by simp)]
  infer_instance

noncomputable instance horizontalCompleteFiltrationCochainDiagram_map_mono
    {i j : EInt} (h : i ≤ j) :
    Mono ((horizontalCompleteFiltrationCochainDiagram K).map (homOfLE h)) := by
  apply HomologicalComplex.mono_of_mono_f
  intro z
  by_cases hz : z ≤ 0
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, z = -(t : ℤ) := by
      refine ⟨(-z).toNat, ?_⟩
      rw [Int.toNat_of_nonneg (by lia)]
      lia
    change Mono ((HomologicalComplex.extendMap
      (horizontalCompleteFilteredTotalMap K h)
        ComplexShape.embeddingDownNat).f (-(t : ℤ)))
    rw [HomologicalComplex.extendMap_f _ _
      (i := t) (i' := -(t : ℤ)) (by simp)]
    infer_instance
  · have hzpos : 0 < z := by lia
    have hsource : IsZero
        (((horizontalCompleteFilteredTotalComplex K i).extend
          ComplexShape.embeddingDownNat).X z) :=
      (horizontalCompleteFilteredTotalComplex K i).isZero_extend_X
        ComplexShape.embeddingDownNat z (fun t ht => by
          simp only [ComplexShape.embeddingDownNat_f] at ht
          lia)
    have htarget : IsZero
        (((horizontalCompleteFilteredTotalComplex K j).extend
          ComplexShape.embeddingDownNat).X z) :=
      (horizontalCompleteFilteredTotalComplex K j).isZero_extend_X
        ComplexShape.embeddingDownNat z (fun t ht => by
          simp only [ComplexShape.embeddingDownNat_f] at ht
          lia)
    exact { right_cancellation := fun g k _ => hsource.eq_of_tgt g k }

private theorem mappingCone_homology_isZero_of_epi_f
    {F G : CochainComplex C ℤ} (f : F ⟶ G) [hfMono : Mono f]
    (n : ℤ) [hfEpi : Epi (f.f n)] :
    IsZero ((CochainComplex.mappingCone f).homology n) := by
  let S : ShortComplex (CochainComplex C ℤ) :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
  let g := CochainComplex.mappingCone.descShortComplex S
  have hgq : QuasiIso g :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hS
  have hcokX : IsZero ((cokernel f).X n) :=
    IsZero.of_iso (isZero_cokernel_of_epi (f.f n))
      (PreservesCokernel.iso (HomologicalComplex.eval C
        (ComplexShape.up ℤ) n) f)
  have hcokH : IsZero ((cokernel f).homology n) :=
    (HomologicalComplex.ExactAt.of_isZero hcokX).isZero_homology
  have hgAt : QuasiIsoAt g n := hgq.quasiIsoAt n
  have hgIso : IsIso (HomologicalComplex.homologyMap g n) :=
    (quasiIsoAt_iff_isIso_homologyMap g n).mp hgAt
  exact IsZero.of_iso hcokH
    (@asIso _ _ _ _ (HomologicalComplex.homologyMap g n) hgIso)

/-- For a nonnegative homological bicomplex K in an abelian
category and i≤j in EInt, if the extended cochain map F_i → F_j
is epic in degree n∈ℤ, then
H^n(Cone(F_i → F_j)) is a zero object.
The complete-filtration map is monic as a cochain map. -/
theorem horizontalCompleteFiltrationSpectralObject_H_isZero_of_epi_f
    {i j : EInt} (h : i ≤ j) (n : ℤ)
    [hfEpi : Epi (((horizontalCompleteFiltrationCochainDiagram K).map
      (homOfLE h)).f n)] :
    IsZero (((horizontalCompleteFiltrationSpectralObject K).H n).obj
      (ComposableArrows.mk₁ (homOfLE h))) := by
  let f := (horizontalCompleteFiltrationCochainDiagram K).map (homOfLE h)
  let M := CochainComplex.mappingCone f
  have hMH : IsZero (M.homology n) :=
    mappingCone_homology_isZero_of_epi_f f n
  change IsZero ((HomotopyCategory.homologyFunctor C
    (ComplexShape.up ℤ) n).obj
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M))
  exact ((HomotopyCategory.homologyFunctorFactors C
    (ComplexShape.up ℤ) n).app M).isZero_iff.mpr hMH

theorem horizontalCompleteFiltrationCochainDiagram_obj_isZero_of_neg
    (a : ℤ) (ha : a < 0) :
    IsZero ((horizontalCompleteFiltrationCochainDiagram K).obj (a : EInt)) := by
  change IsZero ((ComplexShape.embeddingDownNat.extendFunctor C).obj
    (horizontalCompleteFilteredTotalComplex K (a : EInt)))
  rw [horizontalCompleteFilteredTotalComplex_coe_of_neg K a ha]
  exact (ComplexShape.embeddingDownNat.extendFunctor C).map_isZero
    HomologicalComplex.isZero_zero

/-- For a nonnegative homological bicomplex K in an abelian
category and i≤j in EInt, if both extended filtration stages
F_i and F_j are zero complexes, then
H^n(Cone(F_i → F_j)) is zero for every n∈ℤ. -/
theorem horizontalCompleteFiltrationSpectralObject_H_isZero_of_obj_isZero
    {i j : EInt} (h : i ≤ j)
    (hi : IsZero ((horizontalCompleteFiltrationCochainDiagram K).obj i))
    (hj : IsZero ((horizontalCompleteFiltrationCochainDiagram K).obj j))
    (n : ℤ) :
    IsZero (((horizontalCompleteFiltrationSpectralObject K).H n).obj
      (ComposableArrows.mk₁ (homOfLE h))) := by
  let f := (horizontalCompleteFiltrationCochainDiagram K).map (homOfLE h)
  let M := CochainComplex.mappingCone f
  have hMX : IsZero (M.X n) :=
    (CochainComplex.mappingCone.isZero_X_iff f n).2
      ⟨(HomologicalComplex.eval C (ComplexShape.up ℤ) (n + 1)).map_isZero hi,
        (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map_isZero hj⟩
  have hMH : IsZero (M.homology n) :=
    (HomologicalComplex.ExactAt.of_isZero hMX).isZero_homology
  change IsZero ((HomotopyCategory.homologyFunctor C
    (ComplexShape.up ℤ) n).obj
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M))
  exact ((HomotopyCategory.homologyFunctorFactors C
    (ComplexShape.up ℤ) n).app M).isZero_iff.mpr hMH

/-- For a nonnegative homological bicomplex K in an abelian
category, let r≥1, r′=r+1 and (p,q)∈ℕ² have no outgoing
bidegree of shape (−r,r−1). Then p<r, and the interval
F_(p−r′) → F_(p−r) has zero relative homology in degree
−p−q+1. Both endpoint stages are negative finite stages. -/
theorem horizontalCompleteFiltrationSpectralObject_isZero_i₀_le
    (r r' : ℤ) (pq : ℕ × ℕ)
    (hpq : ∀ pq' : ℕ × ℕ,
      ¬(ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).Rel pq pq')
    (n : ℤ)
    (_hn : n =
      CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.deg pq + 1)
    (hrr' : r + 1 = r') (hr : 1 ≤ r) :
    IsZero (((horizontalCompleteFiltrationSpectralObject K).H n).obj
      (ComposableArrows.mk₁ (homOfLE
        (CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.i₀_le
          r r' pq hrr' hr)))) := by
  have hpr : (pq.1 : ℤ) < r := by
    by_contra h
    have hp : 0 ≤ (pq.1 : ℤ) - r := by lia
    have hq : 0 ≤ (pq.2 : ℤ) + r - 1 := by lia
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le hp
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le hq
    exact hpq ⟨p', q'⟩ (by
      simp only [ComplexShape.spectralSequenceNat_rel_iff]
      constructor <;> lia)
  apply horizontalCompleteFiltrationSpectralObject_H_isZero_of_obj_isZero K
  · exact horizontalCompleteFiltrationCochainDiagram_obj_isZero_of_neg K
      ((pq.1 : ℤ) - r') (by lia)
  · exact horizontalCompleteFiltrationCochainDiagram_obj_isZero_of_neg K
      ((pq.1 : ℤ) - r) (by lia)

/-- For a nonnegative homological bicomplex K in an abelian
category, let r≥1, r′=r+1 and (p,q)∈ℕ² have no incoming
bidegree of shape (−r,r−1). Then q<r−1, and the interval
F_(p+r−1) → F_(p+r′−1) has zero relative cochain homology
in degree −p−q−1. Its component in total degree p+q+1 is invertible. -/
theorem horizontalCompleteFiltrationSpectralObject_isZero_i₃_le
    (r r' : ℤ) (pq : ℕ × ℕ)
    (hpq : ∀ pq' : ℕ × ℕ,
      ¬(ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).Rel pq' pq)
    (n : ℤ)
    (hn : n =
      CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.deg pq - 1)
    (hrr' : r + 1 = r') (hr : 1 ≤ r) :
    IsZero (((horizontalCompleteFiltrationSpectralObject K).H n).obj
      (ComposableArrows.mk₁ (homOfLE
        (CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.i₃_le
          r r' pq hrr' hr)))) := by
  have hqr : (pq.2 : ℤ) < r - 1 := by
    by_contra h
    have hp : 0 ≤ (pq.1 : ℤ) + r := by lia
    have hq : 0 ≤ (pq.2 : ℤ) - r + 1 := by lia
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le hp
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le hq
    exact hpq ⟨p', q'⟩ (by
      simp only [ComplexShape.spectralSequenceNat_rel_iff]
      constructor <;> lia)
  let a : ℤ := (pq.1 : ℤ) + r - 1
  let b : ℤ := (pq.1 : ℤ) + r' - 1
  let t : ℕ := pq.1 + pq.2 + 1
  have ha : 0 ≤ a := by dsimp [a]; lia
  have hb : 0 ≤ b := by dsimp [b]; lia
  have hta : t ≤ a.toNat := by
    have ha' := Int.toNat_of_nonneg ha
    dsimp [a, t] at ha' ⊢
    omega
  have htb : t ≤ b.toNat := by
    have hb' := Int.toNat_of_nonneg hb
    dsimp [b, t] at hb' ⊢
    omega
  let hij :=
    CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.i₃_le
      r r' pq hrr' hr
  have hsrc : IsIso ((horizontalCompleteFilteredTotalToTotal K
      (CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.i₃
        r pq hr)).f t) := by
    change IsIso ((horizontalCompleteFilteredTotalToTotal K
      (@WithBotTop.coe ℤ a)).f t)
    exact horizontalCompleteFilteredTotalToTotal_f_isIso_of_nonneg K a ha t hta
  have htgt : IsIso ((horizontalCompleteFilteredTotalToTotal K
      (CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.i₃
        r' pq (by lia))).f t) := by
    change IsIso ((horizontalCompleteFilteredTotalToTotal K
      (@WithBotTop.coe ℤ b)).f t)
    exact horizontalCompleteFilteredTotalToTotal_f_isIso_of_nonneg K b hb t htb
  have hmap : IsIso ((horizontalCompleteFilteredTotalMap K hij).f t) :=
    horizontalCompleteFilteredTotalMap_f_isIso_of_toTotal K hij t
      (hi := hsrc) (hj := htgt)
  have hco : IsIso (((horizontalCompleteFiltrationCochainDiagram K).map
      (homOfLE hij)).f (-(t : ℤ))) :=
    horizontalCompleteFiltrationCochainDiagram_map_f_isIso K hij t
      (hmap := hmap)
  have hepi : Epi (((horizontalCompleteFiltrationCochainDiagram K).map
      (homOfLE hij)).f (-(t : ℤ))) := by
    obtain ⟨inv, _, hinv⟩ := hco.out
    exact SplitEpi.epi { section_ := inv, id := hinv }
  have hz := horizontalCompleteFiltrationSpectralObject_H_isZero_of_epi_f
    K hij (-(t : ℤ)) (hfEpi := hepi)
  have hnt : n = -(t : ℤ) := by
    rw [hn]
    dsimp [t,
      CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological]
    omega
  rw [hnt]
  exact hz

noncomputable instance horizontalCompleteFiltrationSpectralObject_hasSpectralSequence :
    (horizontalCompleteFiltrationSpectralObject K).HasSpectralSequence
      CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological where
  isZero_H_obj_mk₁_i₀_le :=
    horizontalCompleteFiltrationSpectralObject_isZero_i₀_le K
  isZero_H_obj_mk₁_i₃_le :=
    horizontalCompleteFiltrationSpectralObject_isZero_i₃_le K

/-- For a nonnegative homological bicomplex K in an abelian
category C, the complete horizontal filtration defines a
spectral sequence starting at page 1, with page-r differential
shape (p,q) ↦ (p−r,q+r−1) on ℕ².
The first page is the relative homology of consecutive
horizontal filtration stages. -/
noncomputable def horizontalFirstQuadrantSpectralSequence :
    SpectralSequence C
      (fun r => ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) 1 :=
  (horizontalCompleteFiltrationSpectralObject K).spectralSequence
    CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological

end HomologicalComplex₂

end
