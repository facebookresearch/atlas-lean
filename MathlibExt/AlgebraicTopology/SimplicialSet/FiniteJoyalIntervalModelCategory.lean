/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalSSet
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalSmithInput
public import MathlibExt.AlgebraicTopology.SimplicialSet.Presentable
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRecognition
public import MathlibExt.AlgebraicTopology.ModelCategory.Combinatorial
public import MathlibExt.CategoryTheory.MorphismProperty.OfHoms
public import MathlibExt.CategoryTheory.MorphismProperty.IndexEquivalence

/-!
# The model structure for finite-interval testing

Recognition is applied on the designated simplicial category. Its generating
cofibrations are the literal wrapped boundary inclusions, and its weak maps
are the inverse image of the original finite-interval testing class. The
result retains Smith's actual second family, both factorization systems and
cofibrant-generation data at a common regular cardinal.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra

universe u

namespace JoyalSSet

private def boundaryFamily : MorphismProperty JoyalSSet.{u} :=
  .ofHoms (fun n : ℕ => ofSSet.{u}.map (SSet.boundary.{u} n).ι)

private abbrev rawTesting : MorphismProperty SSet.{u} :=
  SSet.joyalInterval.productPrecylinder.{u}.testingEquivalences
    SSet.joyalInterval.auxiliaryAnodyneExtensions.{u}

private abbrev copiedTesting : MorphismProperty JoyalSSet.{u} :=
  rawTesting.{u}.inverseImage forget.{u}

private theorem boundaryFamily_eq_strictMap :
    boundaryFamily.{u} = SSet.modelCategoryQuillen.I.{u}.strictMap ofSSet.{u} := by
  change ofHoms (fun n : ℕ => ofSSet.{u}.map (SSet.boundary.{u} n).ι) =
    (ofHoms (fun n : ℕ => (SSet.boundary.{u} n).ι)).strictMap ofSSet.{u}
  exact (strictMap_ofHoms _ ofSSet.{u}).symm

private theorem boundary_rlp_eq_inverseImage :
    boundaryFamily.{u}.rlp =
      SSet.modelCategoryQuillen.I.{u}.rlp.inverseImage forget.{u} := by
  rw [boundaryFamily_eq_strictMap]
  exact strictMap_rlp_eq_inverseImage_rlp _ _ _ equivalenceSSet.symm.toAdjunction

private theorem boundary_rlp {X Y : JoyalSSet.{u}} (p : X ⟶ Y) :
    boundaryFamily.{u}.rlp p ↔
      SSet.modelCategoryQuillen.I.{u}.rlp (forget.map p) := by
  rw [boundary_rlp_eq_inverseImage]
  rfl

private theorem copied_monomorphisms :
    monomorphisms JoyalSSet.{u} =
      (monomorphisms SSet.{u}).inverseImage forget.{u} := by
  ext X Y f
  change Mono f ↔ Mono (forget.map f)
  constructor
  · intro hf
    let _ : Mono f := hf
    infer_instance
  · exact forget.mono_of_mono_map

private theorem boundary_left :
    boundaryFamily.{u}.rlp.llp = monomorphisms JoyalSSet.{u} := by
  calc
    boundaryFamily.rlp.llp =
        (SSet.modelCategoryQuillen.I.rlp.inverseImage equivalenceSSet.functor).llp :=
      congrArg (fun P : MorphismProperty JoyalSSet.{u} => P.llp)
        boundary_rlp_eq_inverseImage
    _ = SSet.modelCategoryQuillen.I.rlp.llp.inverseImage equivalenceSSet.functor :=
      (inverseImage_llp_of_equivalence equivalenceSSet SSet.modelCategoryQuillen.I.rlp).symm
    _ = (monomorphisms SSet.{u}).inverseImage forget :=
      congrArg (fun P : MorphismProperty SSet.{u} => P.inverseImage forget)
        SSet.modelCategoryQuillen.llp_rlp_I
    _ = monomorphisms JoyalSSet.{u} := copied_monomorphisms.symm

private theorem boundary_right :
    boundaryFamily.{u}.rlp = (monomorphisms JoyalSSet.{u}).rlp := by
  calc
    boundaryFamily.rlp = boundaryFamily.rlp.llp.rlp :=
      boundaryFamily.rlp_llp_rlp.symm
    _ = (monomorphisms JoyalSSet.{u}).rlp :=
      congrArg MorphismProperty.rlp boundary_left

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

private theorem boundary_cardinal :
    boundaryFamily.{u}.IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} := by
  let _ : IsLocallyPresentable.{u} SSet.{u} := SSet.isLocallyPresentable
  let _ : IsLocallyPresentable.{u} JoyalSSet.{u} :=
    equivalenceSSet.symm.isLocallyPresentable
  let _ : HasColimitsOfSize.{u, u} JoyalSSet.{u} :=
    { has_colimits_of_shape := fun J _ => JoyalSSet.hasColimitsOfShape J }
  let _ : boundaryFamily.{u}.IsSmall.{u} := by
    dsimp [boundaryFamily]
    exact isSmall_ofHoms _
  refine {
    isSmall := inferInstance
    locallySmall := inferInstance
    hasPushouts := inferInstance
    hasCoproducts := inferInstance
    hasIterationOfShape := inferInstance
    preservesColimit := ?_ }
  intro A B X Y i hi f hf
  let _ : IsFinitelyPresentable.{u} A := by
    obtain ⟨n⟩ := hi
    exact isCardinalPresentable_of_isEquivalence
      (SSet.boundary.{u} n).toSSet Cardinal.aleph0.{u} ofSSet.{u}
  infer_instance

private theorem boundary_soa : boundaryFamily.{u}.HasSmallObjectArgument.{u} :=
  { exists_cardinal :=
      ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance, boundary_cardinal⟩ }

private theorem copied_trivial_cofibrations :
    boundaryFamily.{u}.rlp.llp ⊓ copiedTesting.{u} =
      (SSet.modelCategoryQuillen.I.{u}.rlp.llp ⊓ rawTesting.{u}).inverseImage
        forget.{u} := by
  rw [boundary_left, SSet.modelCategoryQuillen.llp_rlp_I,
    MorphismProperty.inverseImage_inf, ← copied_monomorphisms]

private theorem copied_smith_input :
    SmithRecognitionInput.{u} (C := JoyalSSet.{u})
      boundaryFamily.{u} copiedTesting.{u} := by
  let hraw := SSet.joyalInterval.smithRecognitionInput.{u}
  let _ : rawTesting.{u}.HasTwoOutOfThreeProperty := hraw.weak_two_out_of_three
  let _ : rawTesting.{u}.IsStableUnderRetracts := hraw.weak_retracts
  let Traw : MorphismProperty SSet.{u} :=
    SSet.modelCategoryQuillen.I.rlp.llp ⊓ rawTesting
  let _ : Traw.IsStableUnderCobaseChange := hraw.trivial_cofibrations_cobase
  let _ : IsStableUnderTransfiniteComposition.{u} Traw :=
    hraw.trivial_cofibrations_transfinite
  refine {
    weak_two_out_of_three := inferInstance
    weak_retracts := inferInstance
    trivial_fibrations_weak := ?_
    trivial_cofibrations_cobase := ?_
    trivial_cofibrations_transfinite := ?_
    solution_set := ?_ }
  · intro X Y p hp
    exact hraw.trivial_fibrations_weak _ ((boundary_rlp p).1 hp)
  · rw [copied_trivial_cofibrations]
    refine { of_isPushout := ?_ }
    intro A A' B B' f g f' g' sq hf
    exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      (P := Traw) (sq.map forget) hf
  · rw [copied_trivial_cofibrations]
    refine { isStableUnderTransfiniteCompositionOfShape := ?_ }
    intro J _ _ _ _
    let _ : PreservesWellOrderContinuousOfShape J forget.{u} :=
      { preservesColimitsOfShape := fun j hj => inferInstance }
    refine { le := ?_ }
    intro X Y f hf
    exact transfiniteCompositionsOfShape_le Traw J (forget.map f)
      hf.some.map.mem
  · intro A B i hi
    have hiRaw : SSet.modelCategoryQuillen.I (forget.map i) := by
      obtain ⟨n⟩ := hi
      exact .mk n
    obtain ⟨S, Q, incoming, hQ⟩ := hraw.solution_set (forget.map i) hiRaw
    let UA := forget.{u}.mapArrow
    let Q' : S → copiedTesting.arrowObjectProperty.FullSubcategory :=
      fun s => ⟨ofSSet.mapArrow.obj (Q s).obj, (Q s).property⟩
    let incoming' (s : S) : Arrow.mk i ⟶
        copiedTesting.arrowObjectProperty.ι.obj (Q' s) :=
      UA.preimage (incoming s)
    refine ⟨S, Q', incoming', ?_⟩
    intro Y h
    let Yraw : rawTesting.arrowObjectProperty.FullSubcategory :=
      ⟨UA.obj Y.obj, Y.property⟩
    obtain ⟨s, g, hg⟩ := hQ Yraw (UA.map h)
    let g' : Q' s ⟶ Y := ObjectProperty.homMk (UA.preimage g.hom)
    refine ⟨s, g', ?_⟩
    apply UA.map_injective
    rw [Functor.map_comp]
    change UA.map (UA.preimage (X := Arrow.mk i) (Y := (Q' s).obj) (incoming s)) ≫
      UA.map (UA.preimage (X := (Q' s).obj) (Y := Y.obj) g.hom) = UA.map h
    rw [UA.map_preimage (X := Arrow.mk i) (Y := (Q' s).obj) (incoming s),
      UA.map_preimage (X := (Q' s).obj) (Y := Y.obj) g.hom]
    exact hg

/-- The full finite-interval testing model, with its actual generating
families and one common cardinal for local presentability and both SOAs.
All model and factorization data are conclusions. -/
theorem exists_finiteJoyalInterval_modelCategory :
    let C := JoyalSSet.{u}
    let I : MorphismProperty C :=
      .ofHoms (fun n : ℕ => ofSSet.{u}.map (SSet.boundary.{u} n).ι)
    let W : MorphismProperty C :=
      (SSet.joyalInterval.productPrecylinder.{u}.testingEquivalences
        SSet.joyalInterval.auxiliaryAnodyneExtensions.{u}).inverseImage forget.{u}
    let Monos := monomorphisms C
    let T := Monos ⊓ W
    let F := T.rlp
    ∃ (s : SmithModelStructureData.{u} (C := C) I W) (M : ModelCategory C),
      letI : ModelCategory C := M
      let G := s.J
      ∃ κ : Cardinal.{u},
      ∃ regular : Fact κ.IsRegular,
      letI : Fact κ.IsRegular := regular
      ∃ bottom : OrderBot κ.ord.ToType,
      letI : OrderBot κ.ord.ToType := bottom
      ∃ cg : CofibrantGenerationData C κ,
        M.categoryWithCofibrations.cofibrations = Monos ∧
        M.categoryWithWeakEquivalences.weakEquivalences = W ∧
        M.categoryWithFibrations.fibrations = F ∧
        trivialCofibrations C = T ∧
        trivialFibrations C = I.rlp ∧
        I.rlp = Monos.rlp ∧
        F ⊓ W = I.rlp ∧
        IsWeakFactorizationSystem Monos I.rlp ∧
        IsWeakFactorizationSystem T F ∧
        G.rlp = F ∧
        G.rlp.llp = T ∧
        G ≤ T ∧
        I.IsSmall.{u} ∧ G.IsSmall.{u} ∧
        I.HasSmallObjectArgument.{u} ∧ G.HasSmallObjectArgument.{u} ∧
        IsCardinalLocallyPresentable C κ ∧
        I.IsCardinalForSmallObjectArgument κ ∧
        G.IsCardinalForSmallObjectArgument κ ∧
        cg.I = I ∧ cg.J = G ∧
        IsCombinatorialModelCategory.{u} C := by
  let I := boundaryFamily.{u}
  let W := copiedTesting.{u}
  let Monos := monomorphisms JoyalSSet.{u}
  let T := Monos ⊓ W
  let F := T.rlp
  let _ : HasLimitsOfSize.{u, u} JoyalSSet.{u} :=
    { has_limits_of_shape := fun J _ => JoyalSSet.hasLimitsOfShape J }
  let _ : HasColimitsOfSize.{u, u} JoyalSSet.{u} :=
    { has_colimits_of_shape := fun J _ => JoyalSSet.hasColimitsOfShape J }
  let _ : IsLocallyPresentable.{u} SSet.{u} := SSet.isLocallyPresentable
  let _ : IsLocallyPresentable.{u} JoyalSSet.{u} :=
    equivalenceSSet.symm.isLocallyPresentable
  let _ : I.HasSmallObjectArgument.{u} := boundary_soa
  let h := copied_smith_input.{u}
  obtain ⟨s⟩ := smithRecognition I W h
  have hLeft : s.J.rlp.llp = T := by
    rw [s.trivialCofibrations_eq, boundary_left]
  have hFib : s.J.rlp = F := by
    rw [s.fibrations_eq, boundary_left]
  have hTF : F ⊓ W = I.rlp := by
    rw [← hFib]
    exact s.trivialFibrations_eq
  have hFirst : IsWeakFactorizationSystem Monos I.rlp := by
    simpa only [I, Monos, boundary_left] using s.cofibration_wfs
  have hSecond : IsWeakFactorizationSystem T F := by
    rw [← hLeft, ← hFib]
    exact s.trivialCofibration_wfs
  let _ : CategoryWithCofibrations JoyalSSet.{u} := ⟨Monos⟩
  let _ : CategoryWithWeakEquivalences JoyalSSet.{u} := ⟨W⟩
  let _ : CategoryWithFibrations JoyalSSet.{u} := ⟨F⟩
  let M : ModelCategory JoyalSSet.{u} :=
    s.modelCategory h.weak_two_out_of_three boundary_left.symm hFib.symm rfl
  have hMCof : M.categoryWithCofibrations.cofibrations = Monos := rfl
  have hMW : M.categoryWithWeakEquivalences.weakEquivalences = W := rfl
  have hMFib : M.categoryWithFibrations.fibrations = F := rfl
  refine ⟨s, M, ?_⟩
  let _ : ModelCategory JoyalSSet.{u} := M
  let _ : s.J.HasSmallObjectArgument.{u} := s.J_smallObject
  obtain ⟨κ, regular, bottom, hLP, hIκ, hGκ⟩ :=
    exists_common_generation_cardinal I s.J
  refine ⟨κ, regular, ?_⟩
  let _ : Fact κ.IsRegular := regular
  refine ⟨bottom, ?_⟩
  let _ : OrderBot κ.ord.ToType := bottom
  have hTCModel : trivialCofibrations JoyalSSet.{u} = T := rfl
  have hTFModel : trivialFibrations JoyalSSet.{u} = I.rlp := hTF
  let cg : CofibrantGenerationData JoyalSSet.{u} κ := {
    I := I
    J := s.J
    I_smallObject := hIκ
    J_smallObject := hGκ
    I_rlp := hTFModel.symm
    J_rlp := hFib }
  have hISmall : I.IsSmall.{u} := hIκ.isSmall
  have hGSmall : s.J.IsSmall.{u} := hGκ.isSmall
  refine ⟨cg, hMCof, hMW, hMFib, hTCModel, hTFModel, boundary_right,
    hTF, hFirst, hSecond, hFib, hLeft,
    s.J.le_llp_rlp.trans hLeft.le, hISmall, hGSmall, boundary_soa,
    s.J_smallObject, hLP, hIκ, hGκ, rfl, rfl, ?_⟩
  exact { exists_cardinal := ⟨κ, regular, bottom, hLP, ⟨cg⟩⟩ }

end JoyalSSet
