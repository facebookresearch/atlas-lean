/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
public import MathlibExt.Algebra.Homology.QuasiIsoColimits
public import MathlibExt.Algebra.Homology.ShortComplex.CokernelSequence
public import MathlibExt.AlgebraicTopology.SimplicialSet.NormalizedColimits
public import MathlibExt.AlgebraicTopology.SimplicialSet.NormalizedCoproduct
public import MathlibExt.AlgebraicTopology.SimplicialSet.HornComplement
public import MathlibExt.AlgebraicTopology.SimplicialSet.NormalizedMonomorphisms
public import MathlibExt.AlgebraicTopology.SimplicialSet.NormalizedQuasiIso

/-!
# Anodyne extensions induce chain quasi-isomorphisms

An anodyne extension of simplicial sets induces a quasi-isomorphism on
normalized and unnormalized chains with coefficients in an arbitrary module
over an arbitrary ring.  The proof computes one horn attachment explicitly
and closes the resulting morphism property under the coproduct, pushout,
sequential-composition, and retract operations in the pinned definition of
`SSet.anodyneExtensions`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory.MorphismProperty
open scoped Simplicial

universe u w v

namespace SSet.AnodyneChainQuasiIso

variable {R : Type u} [Ring R]

private abbrev CoeffTy (R : Type u) [Ring R] := ModuleCat.{u} R

local notation "Coeff" => CoeffTy R

@[instance_reducible]
private def normalizedChainQuasiIsomorphisms (A : Coeff) :
    MorphismProperty SSet.{u} :=
  (HomologicalComplex.quasiIso Coeff (ComplexShape.down ℕ)).inverseImage
    (SSet.normalizedChainComplexFunctorObj A)

@[instance_reducible]
private def normalizedMonoQuasiIsomorphisms (A : Coeff) :
    MorphismProperty SSet.{u} :=
  MorphismProperty.monomorphisms SSet.{u} ⊓
    normalizedChainQuasiIsomorphisms A

private instance normalizedChainQuasiIsomorphisms_isMultiplicative (A : Coeff) :
    (normalizedChainQuasiIsomorphisms A).IsMultiplicative :=
  by
    dsimp only [normalizedChainQuasiIsomorphisms]
    infer_instance

private instance normalizedChainQuasiIsomorphisms_respectsIso (A : Coeff) :
    (normalizedChainQuasiIsomorphisms A).RespectsIso :=
  by
    dsimp only [normalizedChainQuasiIsomorphisms]
    infer_instance

private instance normalizedChainQuasiIsomorphisms_isStableUnderRetracts
    (A : Coeff) :
    (normalizedChainQuasiIsomorphisms A).IsStableUnderRetracts :=
  by
    dsimp only [normalizedChainQuasiIsomorphisms]
    infer_instance

private instance normalizedMonoQuasiIsomorphisms_isMultiplicative (A : Coeff) :
    (normalizedMonoQuasiIsomorphisms A).IsMultiplicative :=
  by
    dsimp only [normalizedMonoQuasiIsomorphisms]
    infer_instance

private instance normalizedMonoQuasiIsomorphisms_respectsIso (A : Coeff) :
    (normalizedMonoQuasiIsomorphisms A).RespectsIso :=
  by
    dsimp only [normalizedMonoQuasiIsomorphisms]
    infer_instance

private instance normalizedMonoQuasiIsomorphisms_isStableUnderRetracts
    (A : Coeff) :
    (normalizedMonoQuasiIsomorphisms A).IsStableUnderRetracts :=
  by
    dsimp only [normalizedMonoQuasiIsomorphisms]
    infer_instance

private theorem normalizedChainQuasiIsomorphisms_stableUnderColimits
    (A : Coeff) (J : Type w) [Category.{v} J]
    [HasColimitsOfShape J (Type u)]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    [(colim (J := J) (C := ModuleCat.{u} R)).PreservesHomology] :
    (normalizedChainQuasiIsomorphisms A).IsStableUnderColimitsOfShape J where
  condition X₁ X₂ c₁ c₂ hc₁ hc₂ α hα φ hφ := by
    let F : SSet.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
      SSet.normalizedChainComplexFunctorObj A
    let _ : PreservesColimit X₁ F := by
      dsimp only [F]
      infer_instance
    let _ : PreservesColimit X₂ F := by
      dsimp only [F]
      infer_instance
    let τ : X₁ ⋙ F ⟶ X₂ ⋙ F := Functor.whiskerRight α F
    have hτ : ∀ j, QuasiIso (τ.app j) := fun j => hα j
    have hs : IsColimit (F.mapCocone c₁) := isColimitOfPreserves F hc₁
    have ht : IsColimit (F.mapCocone c₂) := isColimitOfPreserves F hc₂
    apply HomologicalComplex.quasiIso_of_isColimit_of_objectwise
      τ (F.mapCocone c₁) (F.mapCocone c₂) hs ht (F.map φ)
    · intro j
      change F.map (c₁.ι.app j) ≫ F.map φ =
        F.map (α.app j) ≫ F.map (c₂.ι.app j)
      rw [← F.map_comp, ← F.map_comp, hφ j]
    · exact hτ

private noncomputable instance
    normalizedChainQuasiIsomorphisms_isStableUnderCoproducts (A : Coeff) :
    (normalizedChainQuasiIsomorphisms A).IsStableUnderCoproducts.{u} where
  isStableUnderCoproductsOfShape J := by
    let _ : (colim (J := Discrete J) (C := ModuleCat.{u} R)).PreservesHomology :=
      inferInstance
    exact normalizedChainQuasiIsomorphisms_stableUnderColimits A (Discrete J)

private noncomputable instance
    normalizedChainQuasiIsomorphisms_isStableUnderFilteredColimits (A : Coeff) :
    (normalizedChainQuasiIsomorphisms A).IsStableUnderFilteredColimits.{0, 0} where
  isStableUnderColimitsOfShape J _ _ := by
    let _ : HasFilteredColimitsOfSize.{0, 0} (ModuleCat.{u} R) :=
      hasFilteredColimitsOfSize_of_univLE.{0, 0, u, u}
    let _ : AB5OfSize.{0, 0} (ModuleCat.{u} R) :=
      AB5OfSize_of_univLE.{0, 0, u, u} (ModuleCat.{u} R)
    let _ : (colim (J := J) (C := ModuleCat.{u} R)).PreservesHomology :=
      inferInstance
    exact normalizedChainQuasiIsomorphisms_stableUnderColimits A J

private noncomputable instance
    normalizedMonoQuasiIsomorphisms_isStableUnderCoproducts (A : Coeff) :
    (normalizedMonoQuasiIsomorphisms A).IsStableUnderCoproducts.{u} where
  isStableUnderCoproductsOfShape J := by
    constructor
    intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ
    have hf' (j : Discrete J) :
        MorphismProperty.monomorphisms SSet.{u} (f.app j) ∧
          normalizedChainQuasiIsomorphisms A (f.app j) := by
      simpa only [normalizedMonoQuasiIsomorphisms,
        MorphismProperty.inf_iff] using hf j
    change MorphismProperty.monomorphisms SSet.{u} φ ∧
      normalizedChainQuasiIsomorphisms A φ
    exact ⟨
      MorphismProperty.IsStableUnderColimitsOfShape.condition
        X₁ X₂ c₁ c₂ hc₁ hc₂ f (fun j => (hf' j).1) φ hφ,
      MorphismProperty.IsStableUnderColimitsOfShape.condition
        X₁ X₂ c₁ c₂ hc₁ hc₂ f (fun j => (hf' j).2) φ hφ⟩

private noncomputable instance
    normalizedMonoQuasiIsomorphisms_isStableUnderFilteredColimits (A : Coeff) :
    (normalizedMonoQuasiIsomorphisms A).IsStableUnderFilteredColimits.{0, 0} where
  isStableUnderColimitsOfShape J _ _ := by
    let _ : (MorphismProperty.monomorphisms (Type u)).IsStableUnderColimitsOfShape J :=
      inferInstance
    let _ : (MorphismProperty.monomorphisms SSet.{u}).IsStableUnderColimitsOfShape J := by
      change (MorphismProperty.monomorphisms
        (SimplexCategoryᵒᵖ ⥤ Type u)).IsStableUnderColimitsOfShape J
      rw [← MorphismProperty.functorCategory_monomorphisms]
      infer_instance
    constructor
    intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ
    have hf' (j : J) :
        MorphismProperty.monomorphisms SSet.{u} (f.app j) ∧
          normalizedChainQuasiIsomorphisms A (f.app j) := by
      simpa only [normalizedMonoQuasiIsomorphisms,
        MorphismProperty.inf_iff] using hf j
    change MorphismProperty.monomorphisms SSet.{u} φ ∧
      normalizedChainQuasiIsomorphisms A φ
    exact ⟨
      MorphismProperty.IsStableUnderColimitsOfShape.condition
        X₁ X₂ c₁ c₂ hc₁ hc₂ f (fun j => (hf' j).1) φ hφ,
      MorphismProperty.IsStableUnderColimitsOfShape.condition
        X₁ X₂ c₁ c₂ hc₁ hc₂ f (fun j => (hf' j).2) φ hφ⟩

private noncomputable abbrev hornTop (d : ℕ) :
    (Δ[d + 1] : SSet.{u}).nonDegenerate (d + 1) :=
  SSet.hornTopNonDegenerate d

private noncomputable abbrev hornMissingFace
    (d : ℕ) (k : Fin (d + 2)) :
    (Δ[d + 1] : SSet.{u}).nonDegenerate d :=
  SSet.hornMissingFaceNonDegenerate d k

private theorem hornTop_not_mem (d : ℕ) (k : Fin (d + 2)) :
    (hornTop d).val ∉ (SSet.horn (d + 1) k).obj _ := by
  exact SSet.hornTopNonDegenerate_not_mem d k

private theorem hornMissingFace_not_mem (d : ℕ) (k : Fin (d + 2)) :
    (hornMissingFace d k).val ∉ (SSet.horn (d + 1) k).obj _ := by
  exact SSet.hornMissingFaceNonDegenerate_not_mem d k

private theorem hornOutside_dim_eq_or_eq_add_one
    (d : ℕ) (k : Fin (d + 2)) {q : ℕ}
    (x : (Δ[d + 1] : SSet.{u}).nonDegenerate q)
    (hx : x.val ∉ (SSet.horn (d + 1) k).obj _) :
    q = d ∨ q = d + 1 := by
  exact SSet.horn_nonDegenerate_outside_dimension d k x hx

private theorem hornOutside_eq_top
    (d : ℕ)
    (x : (Δ[d + 1] : SSet.{u}).nonDegenerate (d + 1)) :
    x = hornTop d := by
  exact SSet.horn_nonDegenerate_outside_eq_top d x

private theorem hornOutside_eq_missingFace
    (d : ℕ) (k : Fin (d + 2))
    (x : (Δ[d + 1] : SSet.{u}).nonDegenerate d)
    (hx : x.val ∉ (SSet.horn (d + 1) k).obj _) :
    x = hornMissingFace d k := by
  exact SSet.horn_nonDegenerate_outside_eq_missingFace d k x hx

private theorem mem_range_nonDegenerateEmbedding_horn_iff
    (d : ℕ) (k : Fin (d + 2)) {q : ℕ}
    (x : (Δ[d + 1] : SSet.{u}).nonDegenerate q) :
    x ∈ Set.range
        (SSet.nonDegenerateEmbeddingOfMono (SSet.horn (d + 1) k).ι q) ↔
      x.val ∈ (SSet.horn (d + 1) k).obj _ := by
  exact SSet.mem_range_nonDegenerateEmbedding_horn_iff d k x

private theorem not_mem_range_nonDegenerateEmbedding_horn_iff
    (d : ℕ) (k : Fin (d + 2)) {q : ℕ}
    (x : (Δ[d + 1] : SSet.{u}).nonDegenerate q) :
    x ∉ Set.range
        (SSet.nonDegenerateEmbeddingOfMono (SSet.horn (d + 1) k).ι q) ↔
      x.val ∉ (SSet.horn (d + 1) k).obj _ := by
  exact SSet.not_mem_range_nonDegenerateEmbedding_horn_iff d k x

private abbrev hornNormalizedChainMap (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) :=
  SSet.normalizedChainComplexMap (SSet.horn (d + 1) k).ι A

private abbrev hornRelativeNormalized (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) : ChainComplex Coeff ℕ :=
  Limits.cokernel (hornNormalizedChainMap A d k)

private abbrev hornRelativeπ (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) :
    (Δ[d + 1] : SSet.{u}).normalizedChainComplex A ⟶
      hornRelativeNormalized A d k :=
  Limits.cokernel.π (hornNormalizedChainMap A d k)

private noncomputable def hornTopGenerator (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) :
    A ⟶ (hornRelativeNormalized A d k).X (d + 1) :=
  (Δ[d + 1] : SSet.{u}).ιNormalizedChainComplex
      (R := A) (hornTop d).val ≫
    (hornRelativeπ A d k).f (d + 1)

private noncomputable def hornFaceGenerator (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) :
    A ⟶ (hornRelativeNormalized A d k).X d :=
  (Δ[d + 1] : SSet.{u}).ιNormalizedChainComplex
      (R := A) (hornMissingFace d k).val ≫
    (hornRelativeπ A d k).f d

private theorem iota_comp_hornRelativeπ_eq_zero (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) {q : ℕ}
    (x : (Δ[d + 1] : SSet.{u}).nonDegenerate q)
    (hx : x.val ∈ (SSet.horn (d + 1) k).obj _) :
    (Δ[d + 1] : SSet.{u}).ιNormalizedChainComplex (R := A) x.val ≫
      (hornRelativeπ A d k).f q = 0 := by
  obtain ⟨y, hy⟩ :=
    (mem_range_nonDegenerateEmbedding_horn_iff d k x).2 hx
  have hval : (SSet.horn (d + 1) k).ι.app _ y.val = x.val :=
    congrArg Subtype.val hy
  rw [← hval]
  rw [← SSet.ι_normalizedChainComplexMap_f_assoc]
  rw [← HomologicalComplex.comp_f, Limits.cokernel.condition]
  rfl

private theorem hornTopGenerator_d (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) :
    hornTopGenerator A d k ≫
        (hornRelativeNormalized A d k).d (d + 1) d =
      ((-1 : ℤ) ^ k.val) • hornFaceGenerator A d k := by
  rw [hornTopGenerator, Category.assoc,
    (hornRelativeπ A d k).comm (d + 1) d]
  rw [← Category.assoc, SSet.ιNormalizedChainComplex_d,
    Preadditive.sum_comp]
  rw [Finset.sum_eq_single k]
  · simp only [Preadditive.zsmul_comp]
    congr 1
  · intro j _ hj
    rw [Preadditive.zsmul_comp]
    have hface :
        (ConcreteCategory.hom
            (SimplicialObject.δ (Δ[d + 1] : SSet.{u}) j))
              (hornTop d).val = (hornMissingFace d j).val := by
      simp [hornTop, hornMissingFace,
        SSet.hornTopNonDegenerate,
        SSet.hornMissingFaceNonDegenerate]
    rw [hface, iota_comp_hornRelativeπ_eq_zero A d k]
    · exact smul_zero _
    · simpa [hornMissingFace,
        SSet.hornMissingFaceNonDegenerate] using
        (SSet.objEquiv_symm_δ_mem_horn_iff j k).2 hj
  · simp

private theorem hornRelative_hom_ext_top (A : Coeff)
    (d : ℕ) (k : Fin (d + 2))
    {Z : Coeff}
    {f g : (hornRelativeNormalized A d k).X (d + 1) ⟶ Z}
    (h : hornTopGenerator A d k ≫ f = hornTopGenerator A d k ≫ g) :
    f = g := by
  rw [← cancel_epi ((hornRelativeπ A d k).f (d + 1))]
  apply SSet.normalizedChainComplex_hom_ext
  intro x hx
  by_cases hmem : x ∈ (SSet.horn (d + 1) k).obj _
  · rw [← Category.assoc,
      iota_comp_hornRelativeπ_eq_zero A d k ⟨x, hx⟩ hmem,
      zero_comp, ← Category.assoc,
      iota_comp_hornRelativeπ_eq_zero A d k ⟨x, hx⟩ hmem,
      zero_comp]
  · have hx' : (⟨x, hx⟩ :
        (Δ[d + 1] : SSet.{u}).nonDegenerate (d + 1)) = hornTop d :=
      hornOutside_eq_top d ⟨x, hx⟩
    have hxval : x = (hornTop d).val := congrArg Subtype.val hx'
    rw [hxval]
    exact h

private theorem hornRelative_hom_ext_face (A : Coeff)
    (d : ℕ) (k : Fin (d + 2))
    {Z : Coeff} {f g : (hornRelativeNormalized A d k).X d ⟶ Z}
    (h : hornFaceGenerator A d k ≫ f = hornFaceGenerator A d k ≫ g) :
    f = g := by
  rw [← cancel_epi ((hornRelativeπ A d k).f d)]
  apply SSet.normalizedChainComplex_hom_ext
  intro x hx
  by_cases hmem : x ∈ (SSet.horn (d + 1) k).obj _
  · rw [← Category.assoc,
      iota_comp_hornRelativeπ_eq_zero A d k ⟨x, hx⟩ hmem,
      zero_comp, ← Category.assoc,
      iota_comp_hornRelativeπ_eq_zero A d k ⟨x, hx⟩ hmem,
      zero_comp]
  · have hx' : (⟨x, hx⟩ :
        (Δ[d + 1] : SSet.{u}).nonDegenerate d) = hornMissingFace d k :=
      hornOutside_eq_missingFace d k ⟨x, hx⟩ hmem
    have hxval : x = (hornMissingFace d k).val := congrArg Subtype.val hx'
    rw [hxval]
    exact h

private noncomputable def hornFaceLift (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) :
    ((Δ[d + 1] : SSet.{u}).normalizedChainComplex A).X d ⟶
      (hornRelativeNormalized A d k).X (d + 1) :=
  ((Δ[d + 1] : SSet.{u}).normalizedChainComplexCoproductIso A d).inv ≫
    Limits.Sigma.desc (fun x =>
      if x = hornMissingFace d k then
        ((-1 : ℤ) ^ k.val) • hornTopGenerator A d k
      else 0)

private theorem iota_hornFaceLift (A : Coeff)
    (d : ℕ) (k : Fin (d + 2))
    (x : (Δ[d + 1] : SSet.{u}).nonDegenerate d) :
    (Δ[d + 1] : SSet.{u}).ιNormalizedChainComplex (R := A) x.val ≫
        hornFaceLift A d k =
      if x = hornMissingFace d k then
        ((-1 : ℤ) ^ k.val) • hornTopGenerator A d k
      else 0 := by
  let e := (Δ[d + 1] : SSet.{u}).normalizedChainComplexCoproductIso A d
  calc
    _ = (Limits.Sigma.ι
          (fun _ : (Δ[d + 1] : SSet.{u}).nonDegenerate d => A) x ≫ e.hom) ≫
        (e.inv ≫ Limits.Sigma.desc (fun x =>
          if x = hornMissingFace d k then
            ((-1 : ℤ) ^ k.val) • hornTopGenerator A d k else 0)) := by
      rw [SSet.ι_normalizedChainComplexCoproductIso_hom]
      rfl
    _ = Limits.Sigma.ι
          (fun _ : (Δ[d + 1] : SSet.{u}).nonDegenerate d => A) x ≫
        Limits.Sigma.desc (fun x =>
          if x = hornMissingFace d k then
            ((-1 : ℤ) ^ k.val) • hornTopGenerator A d k else 0) := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by rw [Limits.Sigma.ι_comp_desc]

private theorem hornNormalizedChainMap_f_comp_hornFaceLift (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) :
    (hornNormalizedChainMap A d k).f d ≫ hornFaceLift A d k = 0 := by
  apply SSet.normalizedChainComplex_hom_ext
  intro x hx
  rw [SSet.ι_normalizedChainComplexMap_f_assoc]
  let z := SSet.nonDegenerateEmbeddingOfMono
    (SSet.horn (d + 1) k).ι d ⟨x, hx⟩
  change (Δ[d + 1] : SSet.{u}).ιNormalizedChainComplex z.val ≫
    hornFaceLift A d k = 0
  rw [iota_hornFaceLift]
  split
  · rename_i h
    exfalso
    have hrange : hornMissingFace d k ∈ Set.range
        (SSet.nonDegenerateEmbeddingOfMono (SSet.horn (d + 1) k).ι d) := by
      exact ⟨⟨x, hx⟩, h⟩
    exact (not_mem_range_nonDegenerateEmbedding_horn_iff d k
      (hornMissingFace d k)).2 (hornMissingFace_not_mem d k) hrange
  · rfl

private noncomputable def hornRelativeXIsoComponentCokernel (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) (q : ℕ) :
    (hornRelativeNormalized A d k).X q ≅
      Limits.cokernel ((hornNormalizedChainMap A d k).f q) :=
  PreservesCokernel.iso
    (HomologicalComplex.eval Coeff (ComplexShape.down ℕ) q)
    (hornNormalizedChainMap A d k)

private theorem hornRelativeπ_f_comp_XIso_hom (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) (q : ℕ) :
    (hornRelativeπ A d k).f q ≫
        (hornRelativeXIsoComponentCokernel A d k q).hom =
      Limits.cokernel.π ((hornNormalizedChainMap A d k).f q) := by
  exact PreservesCokernel.π_iso_hom
    (HomologicalComplex.eval Coeff (ComplexShape.down ℕ) q)
    (hornNormalizedChainMap A d k)

private noncomputable def hornFaceToTop (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) :
    (hornRelativeNormalized A d k).X d ⟶
      (hornRelativeNormalized A d k).X (d + 1) :=
  (hornRelativeXIsoComponentCokernel A d k d).hom ≫
    Limits.cokernel.desc (f := (hornNormalizedChainMap A d k).f d)
      (hornFaceLift A d k)
      (hornNormalizedChainMap_f_comp_hornFaceLift A d k)

private theorem hornFaceGenerator_comp_hornFaceToTop (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) :
    hornFaceGenerator A d k ≫ hornFaceToTop A d k =
      ((-1 : ℤ) ^ k.val) • hornTopGenerator A d k := by
  simp only [hornFaceGenerator, hornFaceToTop, Category.assoc]
  rw [← Category.assoc
      ((hornRelativeπ A d k).f d)
      (hornRelativeXIsoComponentCokernel A d k d).hom,
    hornRelativeπ_f_comp_XIso_hom, Limits.cokernel.π_desc,
    iota_hornFaceLift]
  split
  · rfl
  · rename_i h
    exact (h rfl).elim

private theorem hornSign_mul_self (k : ℕ) :
    ((-1 : ℤ) ^ k) * ((-1 : ℤ) ^ k) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

private theorem hornRelative_isZero_X (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) (q : ℕ)
    (hq : q ≠ d ∧ q ≠ d + 1) :
    IsZero ((hornRelativeNormalized A d k).X q) := by
  rw [IsZero.iff_id_eq_zero]
  rw [← cancel_epi ((hornRelativeπ A d k).f q)]
  apply SSet.normalizedChainComplex_hom_ext
  intro x hx
  by_cases hmem : x ∈ (SSet.horn (d + 1) k).obj _
  · rw [← Category.assoc,
      iota_comp_hornRelativeπ_eq_zero A d k ⟨x, hx⟩ hmem,
      zero_comp, ← Category.assoc,
      iota_comp_hornRelativeπ_eq_zero A d k ⟨x, hx⟩ hmem,
      zero_comp]
  · rcases hornOutside_dim_eq_or_eq_add_one d k ⟨x, hx⟩ hmem with h | h
    · exact (hq.1 h).elim
    · exact (hq.2 h).elim

private theorem hornFaceToTop_comp_d (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) :
    hornFaceToTop A d k ≫
        (hornRelativeNormalized A d k).d (d + 1) d = 𝟙 _ := by
  apply hornRelative_hom_ext_face A d k
  rw [← Category.assoc, hornFaceGenerator_comp_hornFaceToTop,
    Preadditive.zsmul_comp, hornTopGenerator_d, smul_smul,
    hornSign_mul_self, one_smul, Category.comp_id]

private theorem d_comp_hornFaceToTop (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) :
    (hornRelativeNormalized A d k).d (d + 1) d ≫
        hornFaceToTop A d k = 𝟙 _ := by
  apply hornRelative_hom_ext_top A d k
  rw [← Category.assoc, hornTopGenerator_d,
    Preadditive.zsmul_comp, hornFaceGenerator_comp_hornFaceToTop,
    smul_smul, hornSign_mul_self, one_smul, Category.comp_id]

private noncomputable def hornContractingHom (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) (i j : ℕ) :
    (hornRelativeNormalized A d k).X i ⟶
      (hornRelativeNormalized A d k).X j := by
  by_cases h : i = d ∧ j = d + 1
  · rcases h with ⟨hi, hj⟩
    subst i
    subst j
    exact hornFaceToTop A d k
  · exact 0

private theorem hornContractingHom_eq_faceToTop (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) :
    hornContractingHom A d k d (d + 1) = hornFaceToTop A d k := by
  unfold hornContractingHom
  split
  · rename_i h
    have hh : h = ⟨rfl, rfl⟩ := Subsingleton.elim _ _
    subst h
    rfl
  · rename_i h
    exact (h ⟨rfl, rfl⟩).elim

private theorem hornContractingHom_eq_zero (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) (i j : ℕ)
    (h : i ≠ d ∨ j ≠ d + 1) :
    hornContractingHom A d k i j = 0 := by
  unfold hornContractingHom
  split
  · rename_i h'
    rcases h with hi | hj
    · exact (hi h'.1).elim
    · exact (hj h'.2).elim
  · rfl

private noncomputable def hornRelativeContractingHomotopy (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) :
    Homotopy (𝟙 (hornRelativeNormalized A d k)) 0 where
  hom := hornContractingHom A d k
  zero i j hij := by
    apply hornContractingHom_eq_zero
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    exact hij (by simp)
  comm i := by
    by_cases hi : i = d
    · subst i
      obtain _ | d := d
      · rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
        simp [hornContractingHom_eq_faceToTop,
          hornFaceToTop_comp_d]
      · rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
        simp [hornContractingHom_eq_faceToTop,
          hornContractingHom_eq_zero, hornFaceToTop_comp_d]
    · by_cases hi' : i = d + 1
      · subst i
        rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
        simp [hornContractingHom_eq_faceToTop,
          hornContractingHom_eq_zero, d_comp_hornFaceToTop]
      · exact (hornRelative_isZero_X A d k i ⟨hi, hi'⟩).eq_of_src _ _

private theorem hornRelative_acyclic (A : Coeff)
    (d : ℕ) (k : Fin (d + 2)) :
    (hornRelativeNormalized A d k).Acyclic := by
  rw [HomologicalComplex.acyclic_iff]
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology,
    IsZero.iff_id_eq_zero]
  simpa using
    (hornRelativeContractingHomotopy A d k).homologyMap_eq i

private theorem quasiIso_normalizedChainComplexMap_hornι
    (A : Coeff) (d : ℕ) (k : Fin (d + 2)) :
    QuasiIso (hornNormalizedChainMap A d k) := by
  let _ : Mono (SSet.horn (d + 1) k).ι := inferInstance
  let _ : Mono (hornNormalizedChainMap A d k) :=
    (inferInstance :
      (SSet.normalizedChainComplexFunctorObj A).PreservesMonomorphisms).preserves _
  rw [HomologicalComplex.quasiIso_iff_acyclic_cokernel]
  exact hornRelative_acyclic A d k

private noncomputable instance
    normalizedMonoQuasiIsomorphisms_isStableUnderCobaseChange (A : Coeff) :
    (normalizedMonoQuasiIsomorphisms A).IsStableUnderCobaseChange where
  of_isPushout {A₀ A₁ B₀ B₁} {f} {g} {f'} {g'} sq hf := by
    rcases hf with ⟨hfmono, hfq⟩
    have hf'mono : MorphismProperty.monomorphisms SSet.{u} f' :=
      MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq hfmono
    let _ : Mono f := hfmono
    let _ : Mono f' := hf'mono
    let F : SSet.{u} ⥤ ChainComplex Coeff ℕ :=
      SSet.normalizedChainComplexFunctorObj A
    have sqF : IsPushout (F.map g) (F.map f) (F.map f') (F.map g') :=
      sq.map F
    let γ : Limits.cokernel (F.map f) ⟶ Limits.cokernel (F.map f') :=
      Limits.cokernel.map (F.map f) (F.map f') (F.map g) (F.map g')
        sqF.flip.w
    let _ : IsIso γ :=
      Limits.isIso_cokernel_map_of_isPushout sqF.flip
    have hqf : QuasiIso (F.map f) := hfq
    refine ⟨hf'mono, ?_⟩
    change QuasiIso (F.map f')
    rw [HomologicalComplex.quasiIso_iff_acyclic_cokernel] at hqf ⊢
    intro i
    exact (hqf i).of_iso (asIso γ)

private theorem hornGenerators_le_normalizedMonoQuasiIsomorphisms (A : Coeff) :
    SSet.modelCategoryQuillen.J.{u} ≤ normalizedMonoQuasiIsomorphisms A := by
  intro X Y f hf
  simp only [SSet.modelCategoryQuillen.J, iSup_iff] at hf
  obtain ⟨d, ⟨k⟩⟩ := hf
  refine ⟨MorphismProperty.monomorphisms.infer_property _, ?_⟩
  exact quasiIso_normalizedChainComplexMap_hornι A d k

private theorem anodyneExtensions_le_normalizedMonoQuasiIsomorphisms
    (A : Coeff) :
    SSet.anodyneExtensions.{u} ≤ normalizedMonoQuasiIsomorphisms A := by
  rw [SSet.anodyneExtensions_eq_retracts_transfiniteCompositionsOfShape,
    MorphismProperty.retracts_le_iff]
  have hcop : MorphismProperty.coproducts.{u} SSet.modelCategoryQuillen.J.{u} ≤
      normalizedMonoQuasiIsomorphisms A :=
    (MorphismProperty.coproducts_le_iff).2
      (hornGenerators_le_normalizedMonoQuasiIsomorphisms A)
  have hpush :
      (MorphismProperty.coproducts.{u}
        SSet.modelCategoryQuillen.J.{u}).pushouts ≤
        normalizedMonoQuasiIsomorphisms A :=
    (MorphismProperty.pushouts_le_iff).2 hcop
  exact le_trans
    (MorphismProperty.transfiniteCompositionsOfShape_monotone
      (J := ℕ) hpush)
    (MorphismProperty.transfiniteCompositionsOfShape_le
      (W := normalizedMonoQuasiIsomorphisms A) (J := ℕ))

/-- An anodyne extension induces a quasi-isomorphism on normalized chains
with coefficients in an arbitrary module over an arbitrary ring. -/
theorem _root_.SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap
    {R : Type u} [Ring R] (A : ModuleCat.{u} R)
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : SSet.anodyneExtensions f) :
    QuasiIso (SSet.normalizedChainComplexMap f A) := by
  exact (anodyneExtensions_le_normalizedMonoQuasiIsomorphisms A f hf).2

/-- An anodyne extension induces a quasi-isomorphism on unnormalized chains
with coefficients in an arbitrary module over an arbitrary ring. -/
theorem _root_.SSet.anodyneExtensions.quasiIso_chainComplexMap
    {R : Type u} [Ring R] (A : ModuleCat.{u} R)
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : SSet.anodyneExtensions f) :
    QuasiIso (SSet.chainComplexMap f A) := by
  let _ : QuasiIso (SSet.normalizedChainComplexMap f A) :=
    SSet.anodyneExtensions.quasiIso_normalizedChainComplexMap A hf
  have hnat :=
    (SSet.fromNormalizedChainComplexNatTrans (C := ModuleCat.{u} R) A).naturality f
  change SSet.normalizedChainComplexMap f A ≫
        Y.fromNormalizedChainComplex A =
      X.fromNormalizedChainComplex A ≫ SSet.chainComplexMap f A at hnat
  have hcomp : QuasiIso
      (X.fromNormalizedChainComplex A ≫ SSet.chainComplexMap f A) := by
    rw [← hnat]
    infer_instance
  let _ : QuasiIso
      (X.fromNormalizedChainComplex A ≫ SSet.chainComplexMap f A) := hcomp
  exact quasiIso_of_comp_left
    (X.fromNormalizedChainComplex A) (SSet.chainComplexMap f A)

end SSet.AnodyneChainQuasiIso
