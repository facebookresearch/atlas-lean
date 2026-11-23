/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CompactlyGenerated.GeneratedByCounit
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Products of compactly generated spaces

This file constructs arbitrary same-carrier-universe products in
`CompactlyGenerated` by compactly generating the ordinary product topology.
It exposes the native-to-ordinary comparison and installs the unique
cartesian monoidal structure selected by those products.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory

namespace CompactlyGenerated

/-- The explicit compactly generated product of a family of spaces. -/
noncomputable abbrev piObj {I : Type v}
    (X : I → CompactlyGenerated.{u, v}) : CompactlyGenerated.{u, v} :=
  TopCat.toCompactlyGenerated.obj
    (TopCat.piFan (fun i ↦ compactlyGeneratedToTop.obj (X i))).pt

/-- Projection from the explicit compactly generated product. -/
noncomputable def piπ {I : Type v}
    (X : I → CompactlyGenerated.{u, v}) (i : I) : piObj X ⟶ X i :=
  TopCat.toCompactlyGenerated.map
      ((TopCat.piFan
        (fun i ↦ compactlyGeneratedToTop.obj (X i))).π.app ⟨i⟩) ≫
    (asIso (adj.unit.app (X i))).inv

/-- The explicit product fan. -/
noncomputable abbrev piFan {I : Type v}
    (X : I → CompactlyGenerated.{u, v}) : Fan X :=
  Fan.mk (piObj X) (piπ X)

/-- The explicit product fan is limiting. -/
noncomputable def piFanIsLimit {I : Type v}
    (X : I → CompactlyGenerated.{u, v}) : IsLimit (piFan X) := by
  let α := fun i ↦ compactlyGeneratedToTop.obj (X i)
  let c := TopCat.toCompactlyGenerated.mapCone (TopCat.piFan α)
  let e : (Discrete.functor α ⋙ TopCat.toCompactlyGenerated) ≅
      Discrete.functor X :=
    Discrete.natIso (fun i ↦ (asIso (adj.unit.app (X i.as))).symm)
  let _ : TopCat.toCompactlyGenerated.{u, v}.IsRightAdjoint :=
    adj.isRightAdjoint
  have hc : IsLimit c :=
    isLimitOfPreserves TopCat.toCompactlyGenerated (TopCat.piFanIsLimit α)
  have hce : IsLimit ((Cone.postcompose e.hom).obj c) :=
    (IsLimit.postcomposeHomEquiv e c).symm hc
  exact IsLimit.ofIsoLimit hce (Cone.ext (Iso.refl _) (fun j => by
    obtain ⟨i⟩ := j
    change TopCat.toCompactlyGenerated.map (TopCat.piπ α i) ≫
        (asIso (adj.unit.app (X i))).inv =
      TopCat.toCompactlyGenerated.map (TopCat.piπ α i) ≫
        (asIso (adj.unit.app (X i))).inv
    rfl))

/-- Compactly generated spaces have arbitrary products indexed in their
carrier universe. -/
noncomputable instance instHasProducts :
    HasProducts.{v} CompactlyGenerated.{u, v} :=
  hasProducts_of_limit_fans piFan piFanIsLimit

/-- The chosen product is canonically isomorphic to the explicit kified
ordinary product. -/
noncomputable def piIsoPi {I : Type v}
    (X : I → CompactlyGenerated.{u, v}) : (∏ᶜ X) ≅ piObj X :=
  (limit.isLimit _).conePointUniqueUpToIso (piFanIsLimit X)

/-- Inclusion of the explicit native product into the ordinary topological
product. -/
noncomputable def piComparisonToTop {I : Type v}
    (X : I → CompactlyGenerated.{u, v}) :
    compactlyGeneratedToTop.obj (piObj X) ⟶
      (TopCat.piFan (fun i ↦ compactlyGeneratedToTop.obj (X i))).pt :=
  adj.counit.app
    (TopCat.piFan (fun i ↦ compactlyGeneratedToTop.obj (X i))).pt

/-- The native-to-ordinary product comparison is the identity on points. -/
@[simp]
theorem piComparisonToTop_apply {I : Type v}
    (X : I → CompactlyGenerated.{u, v}) (x : piObj X) :
    piComparisonToTop X x = x :=
  adjCounit_apply _ _

/-- The explicit comparison agrees with the generic comparison from the
chosen product. -/
theorem piComparisonToTop_generic_coherence {I : Type v}
    (X : I → CompactlyGenerated.{u, v}) :
    compactlyGeneratedToTop.map (piIsoPi X).hom ≫ piComparisonToTop X =
      Limits.piComparison compactlyGeneratedToTop X ≫
        (TopCat.piIsoPi (fun i ↦ compactlyGeneratedToTop.obj (X i))).hom := by
  let α := fun i ↦ compactlyGeneratedToTop.obj (X i)
  apply (TopCat.piFanIsLimit α).hom_ext
  intro j
  obtain ⟨i⟩ := j
  have hComparisonπ : piComparisonToTop X ≫
      (TopCat.piFan (fun i ↦
        compactlyGeneratedToTop.obj (X i))).π.app ⟨i⟩ =
      compactlyGeneratedToTop.map (piπ X i) := by
    let p := (TopCat.piFan
      (fun i ↦ compactlyGeneratedToTop.obj (X i))).π.app ⟨i⟩
    have hCounit : adj.counit.app (compactlyGeneratedToTop.obj (X i)) =
        compactlyGeneratedToTop.map (asIso (adj.unit.app (X i))).inv := by
      apply (cancel_epi (compactlyGeneratedToTop.map (adj.unit.app (X i)))).1
      calc
        compactlyGeneratedToTop.map (adj.unit.app (X i)) ≫
            adj.counit.app (compactlyGeneratedToTop.obj (X i)) = 𝟙 _ :=
          adj.left_triangle_components (X i)
        _ = compactlyGeneratedToTop.map (adj.unit.app (X i)) ≫
            compactlyGeneratedToTop.map (asIso (adj.unit.app (X i))).inv := by
          change 𝟙 _ = compactlyGeneratedToTop.map
            ((asIso (adj.unit.app (X i))).hom ≫
              (asIso (adj.unit.app (X i))).inv)
          rw [Iso.hom_inv_id, compactlyGeneratedToTop.map_id]
    unfold piComparisonToTop piπ
    calc
      adj.counit.app _ ≫ p =
          compactlyGeneratedToTop.map (TopCat.toCompactlyGenerated.map p) ≫
            adj.counit.app (compactlyGeneratedToTop.obj (X i)) :=
        (adj.counit.naturality p).symm
      _ = compactlyGeneratedToTop.map (TopCat.toCompactlyGenerated.map p) ≫
          compactlyGeneratedToTop.map (asIso (adj.unit.app (X i))).inv := by
        rw [hCounit]
      _ = compactlyGeneratedToTop.map
          (TopCat.toCompactlyGenerated.map p ≫
            (asIso (adj.unit.app (X i))).inv) := by
        rw [compactlyGeneratedToTop.map_comp]
  have hPi : (piIsoPi X).hom ≫ piπ X i = Pi.π X i :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (limit.isLimit _) (piFanIsLimit X) ⟨i⟩
  have hTop : (TopCat.piIsoPi α).hom ≫
      TopCat.piπ α i = Pi.π α i := by
    apply TopCat.hom_ext
    ext x
    exact TopCat.piIsoPi_hom_apply α i x
  simp only [Category.assoc]
  rw [hComparisonπ, ← compactlyGeneratedToTop.map_comp, hPi]
  symm
  calc
    (Limits.piComparison compactlyGeneratedToTop X ≫
        (TopCat.piIsoPi α).hom) ≫ TopCat.piπ α i =
      Limits.piComparison compactlyGeneratedToTop X ≫
        ((TopCat.piIsoPi α).hom ≫ TopCat.piπ α i) :=
      Category.assoc _ _ _
    _ = Limits.piComparison compactlyGeneratedToTop X ≫ Pi.π α i := by rw [hTop]
    _ = compactlyGeneratedToTop.map (Pi.π X i) :=
      Limits.piComparison_comp_π compactlyGeneratedToTop X i

/-- The native-to-ordinary product comparison is a homeomorphism exactly
when the ordinary product topology is already compactly generated. -/
theorem piComparisonToTop_isHomeomorph_iff {I : Type v}
    (X : I → CompactlyGenerated.{u, v}) :
    IsHomeomorph (piComparisonToTop X) ↔
      UCompactlyGeneratedSpace.{u}
        ((TopCat.piFan (fun i ↦ compactlyGeneratedToTop.obj (X i))).pt : Type v) := by
  let P := compactHausProbes.{u}
  constructor
  · intro h
    have hCompact : UCompactlyGeneratedSpace.{u}
        (compactlyGeneratedToTop.obj (piObj X) : Type v) :=
      (piObj X).is_compactly_generated
    have hSource : IsGeneratedBy P
        (compactlyGeneratedToTop.obj (piObj X) : Type v) :=
      (isGeneratedBy_compactHausProbes_iff
        (Y := (compactlyGeneratedToTop.obj (piObj X) : Type v))).2 hCompact
    let _ : IsGeneratedBy P
        (compactlyGeneratedToTop.obj (piObj X) : Type v) := hSource
    exact (isGeneratedBy_compactHausProbes_iff
      (Y := ((TopCat.piFan
        (fun i ↦ compactlyGeneratedToTop.obj (X i))).pt : Type v))).1
      h.isQuotientMap.isGeneratedBy
  · intro h
    let _ : UCompactlyGeneratedSpace.{u}
        ((TopCat.piFan (fun i ↦ compactlyGeneratedToTop.obj (X i))).pt : Type v) := h
    let _ : IsGeneratedBy P
        ((TopCat.piFan (fun i ↦ compactlyGeneratedToTop.obj (X i))).pt : Type v) :=
      (isGeneratedBy_compactHausProbes_iff
        (Y := ((TopCat.piFan
          (fun i ↦ compactlyGeneratedToTop.obj (X i))).pt : Type v))).2 h
    let e : (piObj X : Type v) ≃ₜ
        ((TopCat.piFan (fun i ↦ compactlyGeneratedToTop.obj (X i))).pt : Type v) := by
      unfold piObj TopCat.toCompactlyGenerated
      change WithGeneratedByTopology P
          ((TopCat.piFan
            (fun i ↦ compactlyGeneratedToTop.obj (X i))).pt : Type v) ≃ₜ
        ((TopCat.piFan
          (fun i ↦ compactlyGeneratedToTop.obj (X i))).pt : Type v)
      exact IsGeneratedBy.homeomorph
    have he : (fun x : piObj X ↦ piComparisonToTop X x) = e := by
      funext x
      exact piComparisonToTop_apply X x
    change IsHomeomorph (fun x : piObj X ↦ piComparisonToTop X x)
    rw [he]
    exact e.isHomeomorph

private abbrev pairFamily (X Y : CompactlyGenerated.{u, v}) :
    WalkingPair → CompactlyGenerated.{u, v}
  | WalkingPair.left => X
  | WalkingPair.right => Y

private def walkingPairPiEquivProd
    (X Y : CompactlyGenerated.{u, v}) :
    ((TopCat.piFan (fun j : ULift.{v} WalkingPair =>
      compactlyGeneratedToTop.obj
        ((pairFamily X Y ∘ Equiv.ulift.{v, 0}) j))).pt : Type v) ≃
      ↥(compactlyGeneratedToTop.obj X) ×
        ↥(compactlyGeneratedToTop.obj Y) where
  toFun f :=
    (show X from f (ULift.up WalkingPair.left),
      show Y from f (ULift.up WalkingPair.right))
  invFun p
    | ⟨WalkingPair.left⟩ => p.1
    | ⟨WalkingPair.right⟩ => p.2
  left_inv f := by
    funext j
    rcases j with ⟨_ | _⟩ <;> rfl
  right_inv p := by
    rcases p with ⟨x, y⟩
    rfl

private def walkingPairPiHomeomorphProd
    (X Y : CompactlyGenerated.{u, v}) :
    ((TopCat.piFan (fun j : ULift.{v} WalkingPair =>
      compactlyGeneratedToTop.obj
        ((pairFamily X Y ∘ Equiv.ulift.{v, 0}) j))).pt : Type v) ≃ₜ
      ↥(compactlyGeneratedToTop.obj X) ×
        ↥(compactlyGeneratedToTop.obj Y) where
  toEquiv := @walkingPairPiEquivProd.{u, v} X Y
  continuous_toFun := by
    dsimp only [walkingPairPiEquivProd]
    exact (continuous_apply (ULift.up WalkingPair.left)).prodMk
      (continuous_apply (ULift.up WalkingPair.right))
  continuous_invFun := by
    dsimp only [walkingPairPiEquivProd]
    apply continuous_pi
    intro j
    rcases j with ⟨_ | _⟩
    · exact continuous_fst
    · exact continuous_snd

/-- The cartesian monoidal structure selected by the arbitrary products. -/
noncomputable instance instCartesianMonoidalCategory :
    CartesianMonoidalCategory CompactlyGenerated.{u, v} := by
  letI : HasFiniteProducts CompactlyGenerated.{u, v} :=
    hasFiniteProducts_of_hasProducts.{v, v, v + 1}
      CompactlyGenerated.{u, v}
  exact @CartesianMonoidalCategory.ofHasFiniteProducts.{v, v + 1}
    CompactlyGenerated.{u, v} inferInstance inferInstance

private noncomputable def pairProductIsoTensor
    (X Y : CompactlyGenerated.{u, v}) :
    (∏ᶜ pairFamily X Y) ≅ X ⊗ Y := by
  let F : WalkingPair → CompactlyGenerated.{u, v} := pairFamily X Y
  let c : Fan F := Fan.mk (X ⊗ Y) (fun j => match j with
    | WalkingPair.left => CartesianMonoidalCategory.fst X Y
    | WalkingPair.right => CartesianMonoidalCategory.snd X Y)
  let hc : IsLimit c := by
    refine
      { lift := fun s => CartesianMonoidalCategory.lift
          (s.π.app ⟨WalkingPair.left⟩)
          (s.π.app ⟨WalkingPair.right⟩)
        fac := ?_
        uniq := ?_ }
    · rintro s ⟨j⟩
      cases j
      · exact CartesianMonoidalCategory.lift_fst _ _
      · exact CartesianMonoidalCategory.lift_snd _ _
    · intro s m hm
      apply CartesianMonoidalCategory.hom_ext
      · exact (hm ⟨WalkingPair.left⟩).trans
          (CartesianMonoidalCategory.lift_fst _ _).symm
      · exact (hm ⟨WalkingPair.right⟩).trans
          (CartesianMonoidalCategory.lift_snd _ _).symm
  exact (limit.isLimit _).conePointUniqueUpToIso hc

@[simp]
private theorem pairProductIsoTensor_inv_fst
    (X Y : CompactlyGenerated.{u, v}) :
    (pairProductIsoTensor X Y).inv ≫
      Pi.π (pairFamily X Y) WalkingPair.left =
      CartesianMonoidalCategory.fst X Y := by
  unfold pairProductIsoTensor
  simp

@[simp]
private theorem pairProductIsoTensor_inv_snd
    (X Y : CompactlyGenerated.{u, v}) :
    (pairProductIsoTensor X Y).inv ≫
      Pi.π (pairFamily X Y) WalkingPair.right =
      CartesianMonoidalCategory.snd X Y := by
  unfold pairProductIsoTensor
  simp

private noncomputable def binaryKificationIso
    (X Y : CompactlyGenerated.{u, v}) :
    TopCat.toCompactlyGenerated.obj
        (TopCat.of (↥(compactlyGeneratedToTop.obj X) ×
          ↥(compactlyGeneratedToTop.obj Y))) ≅ X ⊗ Y :=
  TopCat.toCompactlyGenerated.mapIso
      (TopCat.isoOfHomeo (walkingPairPiHomeomorphProd X Y).symm) ≪≫
    (@piIsoPi.{u, v} (ULift.{v} WalkingPair)
      (pairFamily X Y ∘ Equiv.ulift.{v, 0})).symm ≪≫
    CategoryTheory.Limits.Pi.reindex (C := CompactlyGenerated.{u, v})
      (Equiv.ulift.{v, 0})
      (pairFamily X Y) ≪≫
    pairProductIsoTensor X Y

@[simp]
private theorem binaryKificationIso_hom_fst
    (X Y : CompactlyGenerated.{u, v}) :
    (binaryKificationIso X Y).hom ≫
        CartesianMonoidalCategory.fst X Y =
      TopCat.toCompactlyGenerated.map
          (TopCat.prodFst :
            TopCat.of (↥(compactlyGeneratedToTop.obj X) ×
              ↥(compactlyGeneratedToTop.obj Y)) ⟶
              compactlyGeneratedToTop.obj X) ≫
        (asIso (adj.unit.app X)).inv := by
  let h : TopCat.of (↥(compactlyGeneratedToTop.obj X) ×
      ↥(compactlyGeneratedToTop.obj Y)) ⟶
      (TopCat.piFan (fun j ↦ compactlyGeneratedToTop.obj
        ((pairFamily X Y ∘ Equiv.ulift.{v, 0}) j))).pt :=
    (TopCat.isoOfHomeo (walkingPairPiHomeomorphProd X Y).symm).hom
  have hRaw : h ≫ (TopCat.piFan (fun j ↦ compactlyGeneratedToTop.obj
      ((pairFamily X Y ∘ Equiv.ulift.{v, 0}) j))).π.app
      ⟨ULift.up WalkingPair.left⟩ =
      (TopCat.prodFst : TopCat.of (↥(compactlyGeneratedToTop.obj X) ×
        ↥(compactlyGeneratedToTop.obj Y)) ⟶
          compactlyGeneratedToTop.obj X) := by
    apply TopCat.hom_ext
    ext p
    rfl
  have hPair : (pairProductIsoTensor X Y).hom ≫
      CartesianMonoidalCategory.fst X Y =
      Pi.π (pairFamily X Y) WalkingPair.left := by
    apply (cancel_epi (pairProductIsoTensor X Y).inv).1
    simp only [Iso.inv_hom_id_assoc,
      pairProductIsoTensor_inv_fst]
  have hReindex :
      (CategoryTheory.Limits.Pi.reindex (C := CompactlyGenerated.{u, v})
          (Equiv.ulift.{v, 0}) (pairFamily X Y)).hom ≫
          Pi.π (pairFamily X Y) WalkingPair.left =
        Pi.π (pairFamily X Y ∘ Equiv.ulift.{v, 0})
          (ULift.up WalkingPair.left) := by
    exact CategoryTheory.Limits.Pi.reindex_hom_π
      (C := CompactlyGenerated.{u, v})
      (Equiv.ulift.{v, 0}) (pairFamily X Y)
      (ULift.up WalkingPair.left)
  have hPi : (piIsoPi
        (pairFamily X Y ∘ Equiv.ulift.{v, 0})).symm.hom ≫
        Pi.π (pairFamily X Y ∘ Equiv.ulift.{v, 0})
          (ULift.up WalkingPair.left) =
      piπ (pairFamily X Y ∘ Equiv.ulift.{v, 0})
        (ULift.up WalkingPair.left) := by
    exact IsLimit.conePointUniqueUpToIso_inv_comp
      (limit.isLimit _)
      (piFanIsLimit (pairFamily X Y ∘ Equiv.ulift.{v, 0}))
      ⟨ULift.up WalkingPair.left⟩
  simp only [binaryKificationIso, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [hPair]
  rw [hReindex]
  calc
    _ = TopCat.toCompactlyGenerated.map h ≫
        piπ (pairFamily X Y ∘ Equiv.ulift.{v, 0})
          (ULift.up WalkingPair.left) := by
      exact congrArg (fun q ↦ TopCat.toCompactlyGenerated.map h ≫ q) hPi
    _ = _ := by
      unfold piπ
      rw [← Category.assoc, ← TopCat.toCompactlyGenerated.map_comp, hRaw]
      rfl

@[simp]
private theorem binaryKificationIso_hom_snd
    (X Y : CompactlyGenerated.{u, v}) :
    (binaryKificationIso X Y).hom ≫
        CartesianMonoidalCategory.snd X Y =
      TopCat.toCompactlyGenerated.map
          (TopCat.prodSnd :
            TopCat.of (↥(compactlyGeneratedToTop.obj X) ×
              ↥(compactlyGeneratedToTop.obj Y)) ⟶
              compactlyGeneratedToTop.obj Y) ≫
        (asIso (adj.unit.app Y)).inv := by
  let h : TopCat.of (↥(compactlyGeneratedToTop.obj X) ×
      ↥(compactlyGeneratedToTop.obj Y)) ⟶
      (TopCat.piFan (fun j ↦ compactlyGeneratedToTop.obj
        ((pairFamily X Y ∘ Equiv.ulift.{v, 0}) j))).pt :=
    (TopCat.isoOfHomeo (walkingPairPiHomeomorphProd X Y).symm).hom
  have hRaw : h ≫ (TopCat.piFan (fun j ↦ compactlyGeneratedToTop.obj
      ((pairFamily X Y ∘ Equiv.ulift.{v, 0}) j))).π.app
      ⟨ULift.up WalkingPair.right⟩ =
      (TopCat.prodSnd : TopCat.of (↥(compactlyGeneratedToTop.obj X) ×
        ↥(compactlyGeneratedToTop.obj Y)) ⟶
          compactlyGeneratedToTop.obj Y) := by
    apply TopCat.hom_ext
    ext p
    rfl
  have hPair : (pairProductIsoTensor X Y).hom ≫
      CartesianMonoidalCategory.snd X Y =
      Pi.π (pairFamily X Y) WalkingPair.right := by
    apply (cancel_epi (pairProductIsoTensor X Y).inv).1
    simp only [Iso.inv_hom_id_assoc,
      pairProductIsoTensor_inv_snd]
  have hReindex :
      (CategoryTheory.Limits.Pi.reindex (C := CompactlyGenerated.{u, v})
          (Equiv.ulift.{v, 0}) (pairFamily X Y)).hom ≫
          Pi.π (pairFamily X Y) WalkingPair.right =
        Pi.π (pairFamily X Y ∘ Equiv.ulift.{v, 0})
          (ULift.up WalkingPair.right) := by
    exact CategoryTheory.Limits.Pi.reindex_hom_π
      (C := CompactlyGenerated.{u, v})
      (Equiv.ulift.{v, 0}) (pairFamily X Y)
      (ULift.up WalkingPair.right)
  have hPi : (piIsoPi
        (pairFamily X Y ∘ Equiv.ulift.{v, 0})).symm.hom ≫
        Pi.π (pairFamily X Y ∘ Equiv.ulift.{v, 0})
          (ULift.up WalkingPair.right) =
      piπ (pairFamily X Y ∘ Equiv.ulift.{v, 0})
        (ULift.up WalkingPair.right) := by
    exact IsLimit.conePointUniqueUpToIso_inv_comp
      (limit.isLimit _)
      (piFanIsLimit (pairFamily X Y ∘ Equiv.ulift.{v, 0}))
      ⟨ULift.up WalkingPair.right⟩
  simp only [binaryKificationIso, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [hPair]
  rw [hReindex]
  calc
    _ = TopCat.toCompactlyGenerated.map h ≫
        piπ (pairFamily X Y ∘ Equiv.ulift.{v, 0})
          (ULift.up WalkingPair.right) := by
      exact congrArg (fun q ↦ TopCat.toCompactlyGenerated.map h ≫ q) hPi
    _ = _ := by
      unfold piπ
      rw [← Category.assoc, ← TopCat.toCompactlyGenerated.map_comp, hRaw]
      rfl

/-- Inclusion of the native binary product into the chosen ordinary TopCat
product. -/
noncomputable def prodComparisonToTop
    (X Y : CompactlyGenerated.{u, v}) :
    compactlyGeneratedToTop.obj (X ⊗ Y) ⟶
      compactlyGeneratedToTop.obj X ⨯ compactlyGeneratedToTop.obj Y :=
  Limits.prod.lift
    (compactlyGeneratedToTop.map (CartesianMonoidalCategory.fst X Y))
    (compactlyGeneratedToTop.map (CartesianMonoidalCategory.snd X Y))

end CompactlyGenerated
