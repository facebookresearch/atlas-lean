/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHCartesianMonoidalModel

/-!
# Tests for the cartesian monoidal CGWH model structure
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory CategoryTheory.Functor
open CategoryTheory.MorphismProperty HomotopicalAlgebra
open scoped MonoidalCategory

namespace MathlibExtTest.CGWH.CartesianMonoidalModel

section ScopeOff

example : CartesianMonoidalCategory CGWH.{u, v} := inferInstance
example : MonoidalClosed CGWH.{u, v} := inferInstance

example : True := by
  fail_if_success
    let _ : ModelCategory CGWH.{u, v} := inferInstance
  fail_if_success
    let _ : BraidedCategory CGWH.{u, v} := inferInstance
  fail_if_success
    let _ : IsClosedSymmetricMonoidalModelCategory CGWH.{u, v} :=
      inferInstance
  trivial

end ScopeOff

section TensorComparison

private noncomputable def explicitTensorIso (X Y : SSet.{v}) :
    SSet.toCGWH.{u, v}.obj (X ⊗ Y) ≅
      SSet.toCGWH.{u, v}.obj X ⊗ SSet.toCGWH.{u, v}.obj Y :=
  SSet.toCGWH.{u, v}.mapIso
      ((CartesianMonoidalCategory.tensorLeftIsoProd X).app Y) ≪≫
    SSet.realizationProdIsoCGWH X Y ≪≫
      ((CartesianMonoidalCategory.tensorLeftIsoProd
        (SSet.toCGWH.{u, v}.obj X)).app
          (SSet.toCGWH.{u, v}.obj Y)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
example (X Y : SSet.{v}) :
    (explicitTensorIso.{u, v} X Y).hom =
      CartesianMonoidalCategory.prodComparison
        SSet.toCGWH.{u, v} X Y := by
  have source_fst :
      ((CartesianMonoidalCategory.tensorLeftIsoProd X).app Y).hom ≫
          Limits.prod.fst =
        CartesianMonoidalCategory.fst X Y :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
      (limit.isLimit _) ⟨WalkingPair.left⟩
  have source_snd :
      ((CartesianMonoidalCategory.tensorLeftIsoProd X).app Y).hom ≫
          Limits.prod.snd =
        CartesianMonoidalCategory.snd X Y :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
      (limit.isLimit _) ⟨WalkingPair.right⟩
  have target_fst :
      ((CartesianMonoidalCategory.tensorLeftIsoProd
        (SSet.toCGWH.{u, v}.obj X)).app
          (SSet.toCGWH.{u, v}.obj Y)).inv ≫
        CartesianMonoidalCategory.fst
          (SSet.toCGWH.{u, v}.obj X)
          (SSet.toCGWH.{u, v}.obj Y) =
      Limits.prod.fst :=
    IsLimit.conePointUniqueUpToIso_inv_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct
        (SSet.toCGWH.{u, v}.obj X)
        (SSet.toCGWH.{u, v}.obj Y))
      (limit.isLimit _) ⟨WalkingPair.left⟩
  have target_snd :
      ((CartesianMonoidalCategory.tensorLeftIsoProd
        (SSet.toCGWH.{u, v}.obj X)).app
          (SSet.toCGWH.{u, v}.obj Y)).inv ≫
        CartesianMonoidalCategory.snd
          (SSet.toCGWH.{u, v}.obj X)
          (SSet.toCGWH.{u, v}.obj Y) =
      Limits.prod.snd :=
    IsLimit.conePointUniqueUpToIso_inv_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct
        (SSet.toCGWH.{u, v}.obj X)
        (SSet.toCGWH.{u, v}.obj Y))
      (limit.isLimit _) ⟨WalkingPair.right⟩
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.prodComparison_fst]
    dsimp only [explicitTensorIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom]
    rw [Category.assoc, Category.assoc, target_fst]
    erw [SSet.realizationProdIsoCGWH_hom_fst]
    rw [← SSet.toCGWH.map_comp, source_fst]
  · rw [CartesianMonoidalCategory.prodComparison_snd]
    dsimp only [explicitTensorIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom]
    rw [Category.assoc, Category.assoc, target_snd]
    erw [SSet.realizationProdIsoCGWH_hom_snd]
    rw [← SSet.toCGWH.map_comp, source_snd]

private noncomputable def tensorNatIso :
    curriedTensorPost SSet.toCGWH.{u, v} ≅
      curriedTensorPre SSet.toCGWH.{u, v} :=
  CartesianMonoidalCategory.prodComparisonBifunctorNatIso
    SSet.toCGWH.{u, v}

example : PreservesLimitsOfShape (Discrete WalkingPair)
    SSet.toCGWH.{u, v} := inferInstance

example {X X' Y Y' : SSet.{v}} (f : X ⟶ X') (g : Y ⟶ Y') :
    SSet.toCGWH.{u, v}.map (f ⊗ₘ g) ≫
        ((tensorNatIso.{u, v}.hom.app X').app Y') =
      ((tensorNatIso.{u, v}.hom.app X).app Y) ≫
        (SSet.toCGWH.{u, v}.map f ⊗ₘ
          SSet.toCGWH.{u, v}.map g) := by
  exact CartesianMonoidalCategory.prodComparison_natural
    SSet.toCGWH.{u, v} f g

#guard_msgs (error, substring := true) in
example (X Y : SSet.{v}) :
    SSet.toCGWH.{u, v}.obj (X ⊗ Y) ≅
      SSet.toCGWH.{u, v}.obj X ⊗ SSet.toCGWH.{u, v}.obj Y :=
  SSet.realizationProdIsoCGWH X Y

end TensorComparison

section ArrowComparison

private noncomputable def pushoutProductIso
    {A B K L : SSet.{v}} (i : A ⟶ B) (j : K ⟶ L) :
    SSet.toCGWH.{u, v}.mapArrow.obj (Arrow.mk i □ Arrow.mk j) ≅
      Arrow.mk (SSet.toCGWH.{u, v}.map i) □
        Arrow.mk (SSet.toCGWH.{u, v}.map j) := by
  let _ : SSet.toCGWH.{u, v}.IsLeftAdjoint :=
    SSet.sSetCGWHAdj.isLeftAdjoint
  let sq := PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i j
  let mappedSq :
      (curriedTensorPost SSet.toCGWH.{u, v}).PushoutObjObj i j :=
    { pt := SSet.toCGWH.obj sq.pt
      inl := SSet.toCGWH.map sq.inl
      inr := SSet.toCGWH.map sq.inr
      isPushout := SSet.toCGWH.map_isPushout sq.isPushout
      ι := SSet.toCGWH.map sq.ι
      inl_ι := by
        rw [← SSet.toCGWH.map_comp, sq.inl_ι]
        rfl
      inr_ι := by
        rw [← SSet.toCGWH.map_comp, sq.inr_ι]
        rfl }
  let targetSq := mappedSq.ofNatIso tensorNatIso.{u, v}
  let standardSq := PushoutObjObj.ofHasPushout
    (curriedTensorPre SSet.toCGWH.{u, v}) i j
  let eLeft := targetSq.isPushout.isoIsPushout _ _ standardSq.isPushout
  change Arrow.mk (SSet.toCGWH.map sq.ι) ≅ Arrow.mk standardSq.ι
  have hι : eLeft.hom ≫ standardSq.ι = targetSq.ι := by
    apply targetSq.isPushout.hom_ext
    · rw [targetSq.isPushout.inl_isoIsPushout_hom_assoc
        _ _ standardSq.isPushout]
      rw [standardSq.inl_ι]
      exact targetSq.inl_ι.symm
    · rw [targetSq.isPushout.inr_isoIsPushout_hom_assoc
        _ _ standardSq.isPushout]
      rw [standardSq.inr_ι]
      exact targetSq.inr_ι.symm
  refine Arrow.isoMk eLeft ((tensorNatIso.{u, v}.app B).app L) ?_
  exact hι

example {A B K L : SSet.{v}} (i : A ⟶ B) (j : K ⟶ L) :
    (pushoutProductIso.{u, v} i j).hom.right =
      ((tensorNatIso.{u, v}.hom.app B).app L) := rfl

example {A B K L : SSet.{v}} (i : A ⟶ B) (j : K ⟶ L) :
    (pushoutProductIso.{u, v} i j).hom.left ≫
        (Arrow.mk (SSet.toCGWH.map i) □
          Arrow.mk (SSet.toCGWH.map j)).hom =
      SSet.toCGWH.map (Arrow.mk i □ Arrow.mk j).hom ≫
        (pushoutProductIso.{u, v} i j).hom.right :=
  (pushoutProductIso.{u, v} i j).hom.w

example {A B K L : SSet.{v}} (i : A ⟶ B) (j : K ⟶ L) : True := by
  let _ : SSet.toCGWH.{u, v}.IsLeftAdjoint :=
    SSet.sSetCGWHAdj.isLeftAdjoint
  let sq := PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i j
  let mappedSq :
      (curriedTensorPost SSet.toCGWH.{u, v}).PushoutObjObj i j :=
    { pt := SSet.toCGWH.obj sq.pt
      inl := SSet.toCGWH.map sq.inl
      inr := SSet.toCGWH.map sq.inr
      isPushout := SSet.toCGWH.map_isPushout sq.isPushout
      ι := SSet.toCGWH.map sq.ι
      inl_ι := by rw [← SSet.toCGWH.map_comp, sq.inl_ι]; rfl
      inr_ι := by rw [← SSet.toCGWH.map_comp, sq.inr_ι]; rfl }
  let targetSq := mappedSq.ofNatIso tensorNatIso.{u, v}
  let standardSq := PushoutObjObj.ofHasPushout
    (curriedTensorPre SSet.toCGWH.{u, v}) i j
  let eLeft := targetSq.isPushout.isoIsPushout _ _ standardSq.isPushout
  have hInl : targetSq.inl ≫ eLeft.hom = standardSq.inl :=
    targetSq.isPushout.inl_isoIsPushout_hom _ _ standardSq.isPushout
  have hInr : targetSq.inr ≫ eLeft.hom = standardSq.inr :=
    targetSq.isPushout.inr_isoIsPushout_hom _ _ standardSq.isPushout
  have hRight : ((tensorNatIso.{u, v}.app B).app L).hom =
      ((tensorNatIso.{u, v}.hom.app B).app L) := rfl
  have hSquare : eLeft.hom ≫ standardSq.ι =
      SSet.toCGWH.map sq.ι ≫
        ((tensorNatIso.{u, v}.hom.app B).app L) := by
    apply targetSq.isPushout.hom_ext
    · rw [targetSq.isPushout.inl_isoIsPushout_hom_assoc
        _ _ standardSq.isPushout, standardSq.inl_ι]
      exact targetSq.inl_ι.symm
    · rw [targetSq.isPushout.inr_isoIsPushout_hom_assoc
        _ _ standardSq.isPushout, standardSq.inr_ι]
      exact targetSq.inr_ι.symm
  clear hInl hInr hRight hSquare
  trivial

#guard_msgs (error, substring := true) in
example {A B K L : SSet.{v}} (i : A ⟶ B) (j : K ⟶ L) :
    (pushoutProductIso.{u, v} i j).hom.right =
      (SSet.realizationProdIsoCGWH B L).hom := by
  rfl

end ArrowComparison

section SelectedScope

open scoped SSet.modelCategoryQuillen CGWH.modelCategory

#synth ModelCategory CGWH.{u, v}
#synth BraidedCategory CGWH.{u, v}
#synth SymmetricCategory CGWH.{u, v}
#synth MonoidalClosed CGWH.{u, v}
#synth IsClosedSymmetricMonoidalModelCategory CGWH.{u, v}

#synth IsClosedSymmetricMonoidalModelCategory CGWH.{0, 0}
#synth IsClosedSymmetricMonoidalModelCategory CGWH.{1, 1}
#synth IsClosedSymmetricMonoidalModelCategory CGWH.{0, 1}
#synth IsClosedSymmetricMonoidalModelCategory CGWH.{1, 0}

section Orthogonals

example :
    ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).rlp =
      trivialFibrations CGWH.{u, v} := by
  rw [strictMap_rlp_eq_inverseImage_rlp _ SSet.toCGWH
    (CGWH.cgwhToTop ⋙ TopCat.toSSet) SSet.sSetCGWHAdj,
    cofibrations_rlp]
  ext X Y f
  let _ : SSet.KanComplex
      ((CGWH.cgwhToTop ⋙ TopCat.toSSet).obj X) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex
      ((CGWH.cgwhToTop ⋙ TopCat.toSSet).obj Y) :=
    TopCat.toSSet_obj_kanComplex _
  change trivialFibrations SSet.{v}
      ((CGWH.cgwhToTop ⋙ TopCat.toSSet).map f) ↔
    trivialFibrations CGWH.{u, v} f
  rw [mem_trivialFibrations_iff, mem_trivialFibrations_iff]
  constructor
  · rintro ⟨hf, hw⟩
    have hfTop : TopCat.realizedHornInclusions.rlp
        (CGWH.cgwhToTop.map f) :=
      (TopCat.hornRLP_iff_toSSet_mem_J_rlp).mpr
        ((SSet.modelCategoryQuillen.fibration_iff _).mp hf)
    have hfCGWH : CGWH.modelFibrations f := by
      change CompactlyGenerated.modelFibrations
        (CGWH.cgwhToCompactlyGenerated.map f)
      change TopCat.realizedHornInclusions.rlp
        (CGWH.cgwhToTop.map f)
      exact hfTop
    have hwKan : SSet.KanComplex.W
        ((CGWH.cgwhToTop ⋙ TopCat.toSSet).map f) :=
      (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mpr
        ((weakEquivalence_iff _).mp hw)
    have hwTop : TopCat.weakHomotopyEquivalences
        (CGWH.cgwhToTop.map f) :=
      (TopCat.mem_weakHomotopyEquivalences_iff _).mpr hwKan
    have hwCGWH : CGWH.weakHomotopyEquivalences f := by
      change CompactlyGenerated.weakHomotopyEquivalences
        (CGWH.cgwhToCompactlyGenerated.map f)
      change TopCat.weakHomotopyEquivalences
        (CGWH.cgwhToTop.map f)
      exact hwTop
    exact ⟨(fibration_iff f).mpr hfCGWH,
      (weakEquivalence_iff f).mpr hwCGWH⟩
  · rintro ⟨hf, hw⟩
    have hfCGWH : CGWH.modelFibrations f := (fibration_iff f).mp hf
    have hfTop : TopCat.realizedHornInclusions.rlp
        (CGWH.cgwhToTop.map f) := by
      change CompactlyGenerated.modelFibrations
        (CGWH.cgwhToCompactlyGenerated.map f) at hfCGWH
      change TopCat.realizedHornInclusions.rlp
        (CGWH.cgwhToTop.map f) at hfCGWH
      exact hfCGWH
    have hwCGWH : CGWH.weakHomotopyEquivalences f :=
      (weakEquivalence_iff f).mp hw
    have hwTop : TopCat.weakHomotopyEquivalences
        (CGWH.cgwhToTop.map f) := by
      change CompactlyGenerated.weakHomotopyEquivalences
        (CGWH.cgwhToCompactlyGenerated.map f) at hwCGWH
      change TopCat.weakHomotopyEquivalences
        (CGWH.cgwhToTop.map f) at hwCGWH
      exact hwCGWH
    exact ⟨
      (SSet.modelCategoryQuillen.fibration_iff _).mpr
        ((TopCat.hornRLP_iff_toSSet_mem_J_rlp).mp hfTop),
      (weakEquivalence_iff _).mpr
        ((SSet.KanComplex.W_iff_realizationWeakEquivalence _).mp
          ((TopCat.mem_weakHomotopyEquivalences_iff _).mp hwTop))⟩

example :
    ((trivialCofibrations SSet.{v}).strictMap
      SSet.toCGWH.{u, v}).rlp = fibrations CGWH.{u, v} := by
  rw [strictMap_rlp_eq_inverseImage_rlp _ SSet.toCGWH
    (CGWH.cgwhToTop ⋙ TopCat.toSSet) SSet.sSetCGWHAdj,
    trivialCofibrations_rlp]
  ext X Y f
  change fibrations SSet.{v}
      ((CGWH.cgwhToTop ⋙ TopCat.toSSet).map f) ↔
    fibrations CGWH.{u, v} f
  constructor
  · intro hf
    change CGWH.modelFibrations f
    change TopCat.realizedHornInclusions.rlp (CGWH.cgwhToTop.map f)
    exact (TopCat.hornRLP_iff_toSSet_mem_J_rlp).mpr
      ((SSet.modelCategoryQuillen.fibration_iff _).mp
        ((fibration_iff _).mpr hf))
  · intro hf
    have hfCGWH : CGWH.modelFibrations f := by
      change CGWH.modelFibrations f at hf
      exact hf
    rw [← fibration_iff]
    apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
    apply (TopCat.hornRLP_iff_toSSet_mem_J_rlp).mp
    change TopCat.realizedHornInclusions.rlp
      (CGWH.cgwhToTop.map f) at hfCGWH
    exact hfCGWH

end Orthogonals

section Clauses

variable {A B K L : CGWH.{u, v}} (i : A ⟶ B) (j : K ⟶ L)

example (hi : cofibrations CGWH.{u, v} i)
    (hj : cofibrations CGWH.{u, v} j) :
    cofibrations CGWH.{u, v} ((Arrow.mk i □ Arrow.mk j).hom) :=
  IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct
    i j hi hj

example (hi : trivialCofibrations CGWH.{u, v} i)
    (hj : cofibrations CGWH.{u, v} j) :
    trivialCofibrations CGWH.{u, v}
      ((Arrow.mk i □ Arrow.mk j).hom) :=
  IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
    i j hi hj

example (hi : cofibrations CGWH.{u, v} i)
    (hj : trivialCofibrations CGWH.{u, v} j) :
    trivialCofibrations CGWH.{u, v}
      ((Arrow.mk i □ Arrow.mk j).hom) :=
  IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right
    i j hi hj

end Clauses

example : IsCofibrant (𝟙_ CGWH.{u, v}) := by
  let e : CGWH.point.{u, v} ≅ 𝟙_ CGWH.{u, v} :=
    CGWH.point_isTerminal.uniqueUpToIso
      CartesianMonoidalCategory.isTerminalTensorUnit
  let eArrow : Arrow.mk (initial.to CGWH.point.{u, v}) ≅
      Arrow.mk (initial.to (𝟙_ CGWH.{u, v})) :=
    Arrow.isoMk (Iso.refl _) e (initialIsInitial.hom_ext _ _)
  rw [isCofibrant_iff, cofibration_iff]
  apply ((cofibrations CGWH.{u, v}).arrow_mk_iso_iff eArrow).mp
  rw [← cofibration_iff, ← isCofibrant_iff]
  exact CGWH.point_isCofibrant

example : CartesianPushoutProductAxiom (C := CGWH.{u, v}) :=
  IsClosedSymmetricMonoidalModelCategory.cartesianPushoutProductAxiom

example : CartesianPullbackHomAxiom (C := CGWH.{u, v}) :=
  IsClosedSymmetricMonoidalModelCategory.cartesianPullbackHomAxiom

example (A B : CGWH.{u, v}) : (ihom A).obj B = CGWH.internalHom A B :=
  CGWH.ihom_obj_eq_internalHom A B

section DeletedOrientationFalsifiers

variable
  (_hcof : ∀ {A B K L : CGWH.{u, v}} (i : A ⟶ B) (j : K ⟶ L),
    cofibrations CGWH.{u, v} i → cofibrations CGWH.{u, v} j →
      cofibrations CGWH.{u, v} ((Arrow.mk i □ Arrow.mk j).hom))
  (_hleft : ∀ {A B K L : CGWH.{u, v}} (i : A ⟶ B) (j : K ⟶ L),
    trivialCofibrations CGWH.{u, v} i → cofibrations CGWH.{u, v} j →
      trivialCofibrations CGWH.{u, v} ((Arrow.mk i □ Arrow.mk j).hom))
  (_hright : ∀ {A B K L : CGWH.{u, v}} (i : A ⟶ B) (j : K ⟶ L),
    cofibrations CGWH.{u, v} i → trivialCofibrations CGWH.{u, v} j →
      trivialCofibrations CGWH.{u, v} ((Arrow.mk i □ Arrow.mk j).hom))
  (_hunit : Nonempty (MonoidalUnitAxiomWitness CGWH.{u, v}))

example : True := by
  fail_if_success
    exact ({
      cofibration_pushoutProduct := _hcof
      trivial_pushoutProduct_right := _hright
      unit_axiom := _hunit } :
        IsClosedSymmetricMonoidalModelCategory CGWH.{u, v})
  trivial

example : True := by
  fail_if_success
    exact ({
      cofibration_pushoutProduct := _hcof
      trivial_pushoutProduct_left := _hleft
      unit_axiom := _hunit } :
        IsClosedSymmetricMonoidalModelCategory CGWH.{u, v})
  trivial

end DeletedOrientationFalsifiers

end SelectedScope

section ScopeTeardown

example : True := by
  fail_if_success
    let _ : ModelCategory CGWH.{u, v} := inferInstance
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  fail_if_success
    let _ : IsClosedSymmetricMonoidalModelCategory CGWH.{u, v} :=
      inferInstance
  trivial

end ScopeTeardown

section Privacy

#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.cgwhRealizationTensorNatIso
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.cgwhRealizationPushoutProductIso
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.cgwhFreeCofibration_rlp_eq
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.cgwhFreeTrivialCofibration_rlp_eq
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.cgwhCartesianFreeCofibrationCofibration
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.cgwhCartesianFreeTrivialCofibrationLeft
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.cgwhCartesianFreeTrivialCofibrationRight
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.cgwhCartesianCofibrationPushoutProduct
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.cgwhCartesianTrivialPushoutProductLeft
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.cgwhCartesianTrivialPushoutProductRight
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.cgwhCartesianUnitIsCofibrant

end Privacy

section Nonclaims

#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.realizationMonoidal
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.monoidAxiom
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.hMonoidal
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.flatCofibrantObjects
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.combinatorialModelCategory
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.localizedModelCategory
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.pointedSmashModelCategory
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.barModelCategory
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.spectraModelCategory

end Nonclaims

#print axioms CGWH.modelCategory.instBraidedCategory
#print axioms
  CGWH.modelCategory.instIsClosedSymmetricMonoidalModelCategory

end MathlibExtTest.CGWH.CartesianMonoidalModel
