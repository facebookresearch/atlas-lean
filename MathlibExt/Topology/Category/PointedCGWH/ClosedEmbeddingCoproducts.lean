/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.Basic
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellCoproducts
public import MathlibExt.Topology.Category.CGWH.PointPushout
public import MathlibExt.Topology.Maps.CollapsedAxes
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Closed embeddings in actual pointed CGWH coproducts

The coproduct is the native unpointed coproduct with its entire family of
basepoints collapsed to the shared native point. Actual colimit cofans identify
this presentation with the chosen pointed coproduct. Closed embeddings descend
through the two complete one-class quotient kernels. The empty family is
handled by the true initial pointed object, not a surjective empty projection.
No model or monoidal premise is used.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v wJ vJ
open CategoryTheory Limits Topology

namespace PointedCGWH

variable {J : Type v}

/-- The actual native coproduct of the family of selected basepoint arrows. -/
def coproductBasepointMap (X : J → PointedCGWH.{u, v}) :
    (∐ fun _ : J => CGWH.point.{u, v}) ⟶ ∐ fun j => (X j).right :=
  Limits.Sigma.map (fun j => (X j).hom)

/-- The actual native pushout collapsing all summand basepoints to the shared point. -/
def coproductPointPresentation (X : J → PointedCGWH.{u, v}) :
    PointedCGWH.{u, v} :=
  Under.mk (pushout.inr (coproductBasepointMap X)
    (CGWH.point_isTerminal.from (∐ fun _ : J => CGWH.point.{u, v})))

private theorem pointCoprojection_terminal (j : J) :
    Limits.Sigma.ι (fun _ : J => CGWH.point.{u, v}) j ≫
        CGWH.point_isTerminal.from (∐ fun _ : J => CGWH.point.{u, v}) =
      𝟙 CGWH.point :=
  CGWH.point_isTerminal.hom_ext _ _

/-- The actual pointed coprojection into the shared-point native pushout. -/
def coproductPointInjection (X : J → PointedCGWH.{u, v}) (j : J) :
    X j ⟶ coproductPointPresentation X :=
  Under.homMk
    (Limits.Sigma.ι (fun j => (X j).right) j ≫
      pushout.inl (coproductBasepointMap X)
        (CGWH.point_isTerminal.from (∐ fun _ : J => CGWH.point.{u, v})))
    (by
      change (X j).hom ≫ Limits.Sigma.ι (fun j => (X j).right) j ≫
        pushout.inl (coproductBasepointMap X) _ = pushout.inr _ _
      have hι : Limits.Sigma.ι (fun _ : J => CGWH.point.{u, v}) j ≫
          coproductBasepointMap X =
        (X j).hom ≫ Limits.Sigma.ι (fun j => (X j).right) j :=
        Limits.Sigma.ι_map (fun j => (X j).hom) j
      calc
        _ = (Limits.Sigma.ι (fun _ : J => CGWH.point.{u, v}) j ≫
            coproductBasepointMap X) ≫ pushout.inl _ _ := by
          simpa only [Category.assoc] using
            congrArg (fun q => q ≫ pushout.inl (coproductBasepointMap X) _) hι.symm
        _ = Limits.Sigma.ι (fun _ : J => CGWH.point.{u, v}) j ≫
            CGWH.point_isTerminal.from (∐ fun _ : J => CGWH.point.{u, v}) ≫
              pushout.inr _ _ := by rw [Category.assoc, pushout.condition]
        _ = _ := by rw [← Category.assoc, pointCoprojection_terminal, Category.id_comp])

/-- The actual pointed cofan of native coprojections into the shared-point presentation. -/
def coproductPointCofan (X : J → PointedCGWH.{u, v}) : Cofan X :=
  Cofan.mk (coproductPointPresentation X) (coproductPointInjection X)

private theorem presentationDesc_condition
    (X : J → PointedCGWH.{u, v}) (s : Cofan X) :
    coproductBasepointMap X ≫
        Limits.Sigma.desc (fun j => (s.inj j).right) =
      CGWH.point_isTerminal.from (∐ fun _ : J => CGWH.point.{u, v}) ≫ s.pt.hom := by
  apply Limits.Sigma.hom_ext
  intro j
  rw [← Category.assoc]
  change (Limits.Sigma.ι (fun _ : J => CGWH.point.{u, v}) j ≫
    Limits.Sigma.map (fun j => (X j).hom)) ≫ _ = _
  rw [Limits.Sigma.ι_map, Category.assoc, Limits.Sigma.ι_comp_desc]
  rw [← Category.assoc, pointCoprojection_terminal, Category.id_comp]
  exact (s.inj j).w

/-- Descend an original pointed cofan through the shared-point native pushout. -/
def coproductPointDesc (X : J → PointedCGWH.{u, v}) (s : Cofan X) :
    coproductPointPresentation X ⟶ s.pt :=
  Under.homMk
    (pushout.desc (Limits.Sigma.desc (fun j => (s.inj j).right)) s.pt.hom
      (by exact presentationDesc_condition X s))
    (by
      change pushout.inr _ _ ≫ pushout.desc _ _ _ = _
      exact pushout.inr_desc _ _ _)

/-- The shared-point presentation is the coproduct of the original pointed family. -/
def coproductPointCofanIsColimit (X : J → PointedCGWH.{u, v}) :
    IsColimit (coproductPointCofan X) :=
  Cofan.IsColimit.mk _
    (coproductPointDesc X)
    (fun s j => by
      apply Under.UnderMorphism.ext
      change (Limits.Sigma.ι (fun j => (X j).right) j ≫ pushout.inl _ _) ≫
        pushout.desc _ _ _ = (s.inj j).right
      rw [Category.assoc, pushout.inl_desc, Limits.Sigma.ι_comp_desc])
    (fun s m hm => by
      dsimp only [coproductPointCofan, Cofan.mk_pt] at m hm
      let mR : pushout (coproductBasepointMap X)
          (CGWH.point_isTerminal.from (∐ fun _ : J => CGWH.point.{u, v})) ⟶ s.pt.right :=
        m.right
      apply Under.UnderMorphism.ext
      change mR = pushout.desc (Limits.Sigma.desc (fun j => (s.inj j).right))
        s.pt.hom (presentationDesc_condition X s)
      apply pushout.hom_ext
      · apply Limits.Sigma.hom_ext
        intro j
        rw [pushout.inl_desc, Limits.Sigma.ι_comp_desc]
        have hRight := congrArg (fun q : X j ⟶ s.pt => q.right) (hm j)
        change Limits.Sigma.ι (fun j => (X j).right) j ≫ pushout.inl _ _ ≫ mR = _ at hRight
        exact hRight
      · rw [pushout.inr_desc]
        exact m.w)

/-- The chosen pointed coproduct identifies with its actual shared-point native pushout. -/
def coproductPointIso (X : J → PointedCGWH.{u, v}) :
    (∐ X) ≅ coproductPointPresentation X :=
  colimit.isoColimitCocone
    ⟨coproductPointCofan X, coproductPointCofanIsColimit X⟩

/-- The presentation comparison preserves each original pointed coprojection. -/
theorem coproductPointIso_ι (X : J → PointedCGWH.{u, v}) (j : J) :
    Limits.Sigma.ι X j ≫ (coproductPointIso X).hom =
      (coproductPointCofan X).inj j := by
  exact colimit.isoColimitCocone_ι_hom
    ⟨coproductPointCofan X, coproductPointCofanIsColimit X⟩ ⟨j⟩

private theorem pointArrow_isClosedEmbedding (X : PointedCGWH.{u, v}) :
    IsClosedEmbedding (ConcreteCategory.hom X.hom) := by
  let _ : Subsingleton CGWH.point.{u, v} := by
    change Subsingleton PUnit.{v + 1}
    infer_instance
  exact ⟨IsEmbedding.of_subsingleton _, (Set.finite_range _).isClosed⟩

private theorem basepointMap_isClosedEmbedding (X : J → PointedCGWH.{u, v}) :
    IsClosedEmbedding (ConcreteCategory.hom (coproductBasepointMap X)) := by
  have hNative :
      (TopCat.closedEmbeddings.inverseImage CGWH.cgwhToTop)
        (Limits.Sigma.map (fun j => (X j).hom)) := by
    apply MorphismProperty.colimMap
    rintro ⟨j⟩
    exact pointArrow_isClosedEmbedding (X j)
  exact hNative

private theorem pointQuotient_kernel
    (f : Arrow TopCat.{v}) [Nonempty f.left]
    (hf : IsClosed (Set.range f.hom)) (x y : f.right) :
    (TopCat.pointQuotientProjection.app f).hom x =
        (TopCat.pointQuotientProjection.app f).hom y ↔
      x = y ∨ (x ∈ Set.range f.hom ∧ y ∈ Set.range f.hom) := by
  let q := (TopCat.pointQuotientProjection.app f).hom
  let p := TopCat.pointQuotientPoint f PUnit.unit
  have hmem (z : f.right) : z ∈ Set.range f.hom ↔ q z = p := by
    rw [← TopCat.pointQuotientProjection_preimage_singleton f]
    rfl
  have hInjective : Function.Injective
      (({p} : Set (TopCat.pointQuotient f))ᶜ |>.restrictPreimage q) :=
    (TopCat.pointQuotientProjection_isHomeomorph_compl_of_isClosed_range f hf).injective
  constructor
  · intro hxy
    by_cases hx : q x = p
    · exact Or.inr ⟨(hmem x).2 hx, (hmem y).2 (hxy.symm.trans hx)⟩
    · left
      have hy : q y ≠ p := fun hy => hx (hxy.trans hy)
      have hx' : q x ∈ ({p} : Set (TopCat.pointQuotient f))ᶜ := hx
      have hy' : q y ∈ ({p} : Set (TopCat.pointQuotient f))ᶜ := hy
      have hSub : (⟨x, hx'⟩ : q ⁻¹' ({p} : Set (TopCat.pointQuotient f))ᶜ) =
          ⟨y, hy'⟩ :=
        hInjective (Subtype.ext hxy)
      exact congrArg Subtype.val hSub
  · rintro (hxy | ⟨hx, hy⟩)
    · exact congrArg q hxy
    · exact (hmem x).1 hx |>.trans ((hmem y).1 hy).symm

private theorem nativePointPushout_kernel
    {W X : CGWH.{u, v}} (i : W ⟶ X) [Nonempty W]
    (hi : IsClosedEmbedding (ConcreteCategory.hom i)) (x y : X) :
    pushout.inl i (CGWH.point_isTerminal.from W) x =
        pushout.inl i (CGWH.point_isTerminal.from W) y ↔
      x = y ∨ (x ∈ Set.range i ∧ y ∈ Set.range i) := by
  let g : W ⟶ CGWH.point := CGWH.point_isTerminal.from W
  let T := CGWH.cgwhToTop.{u, v}
  let e := CGWH.pushoutClosedComparisonIso i g hi
  have hPoint : T.map g = TopCat.isTerminalPUnit.from (T.obj W) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro w
    change (g w : PUnit.{v + 1}) = PUnit.unit
    exact @Subsingleton.elim PUnit.{v + 1} inferInstance _ _
  have hLeg := CGWH.pushoutClosedComparisonIso_hom_inl i g hi
  have hRaw (x y : X) :
      (pushout.inl (T.map i) (T.map g)).hom x =
          (pushout.inl (T.map i) (T.map g)).hom y ↔
        x = y ∨ (x ∈ Set.range i ∧ y ∈ Set.range i) := by
    rw [hPoint]
    let _ : Nonempty (Arrow.mk (T.map i)).left := by
      change Nonempty W
      infer_instance
    exact pointQuotient_kernel (Arrow.mk (T.map i)) hi.isClosed_range x y
  have hComparison (z : X) :
      e.hom ((pushout.inl (T.map i) (T.map g)) z) =
        pushout.inl i g z := by
    exact ConcreteCategory.congr_hom hLeg z
  rw [← hComparison x, ← hComparison y]
  exact (TopCat.homeoOfIso e).injective.eq_iff.trans (hRaw x y)

private theorem basepointMap_natural
    (A B : J → PointedCGWH.{u, v}) (f : ∀ j, A j ⟶ B j) :
    coproductBasepointMap A ≫ Limits.Sigma.map (fun j => (f j).right) =
      coproductBasepointMap B := by
  apply Limits.Sigma.hom_ext
  intro j
  change (Limits.Sigma.ι (fun _ : J => CGWH.point.{u, v}) j ≫
    Limits.Sigma.map (fun j => (A j).hom)) ≫ _ = _
  rw [Limits.Sigma.ι_map, Category.assoc, Limits.Sigma.ι_map]
  rw [← Category.assoc, (f j).w]
  exact (Limits.Sigma.ι_map (fun j => (B j).hom) j).symm

private def presentationMap (A B : J → PointedCGWH.{u, v})
    (f : ∀ j, A j ⟶ B j) :
    coproductPointPresentation A ⟶ coproductPointPresentation B :=
  Under.homMk
    (pushout.desc
      (Limits.Sigma.map (fun j => (f j).right) ≫
        pushout.inl (coproductBasepointMap B)
          (CGWH.point_isTerminal.from (∐ fun _ : J => CGWH.point.{u, v})))
      (pushout.inr (coproductBasepointMap B)
        (CGWH.point_isTerminal.from (∐ fun _ : J => CGWH.point.{u, v})))
      (by
        rw [← Category.assoc, basepointMap_natural, pushout.condition]))
    (by
      change pushout.inr _ _ ≫ pushout.desc _ _ _ = _
      exact pushout.inr_desc _ _ _)

private theorem presentationMap_natural
    (A B : J → PointedCGWH.{u, v}) (f : ∀ j, A j ⟶ B j) :
    (coproductPointIso A).hom ≫ presentationMap A B f =
      Limits.Sigma.map f ≫ (coproductPointIso B).hom := by
  apply Limits.Sigma.hom_ext
  intro j
  rw [← Category.assoc, coproductPointIso_ι]
  rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, coproductPointIso_ι]
  apply Under.UnderMorphism.ext
  change (Limits.Sigma.ι (fun j => (A j).right) j ≫ pushout.inl _ _) ≫
      pushout.desc _ _ _ =
    (f j).right ≫ Limits.Sigma.ι (fun j => (B j).right) j ≫ pushout.inl _ _
  rw [Category.assoc, pushout.inl_desc, ← Category.assoc, Limits.Sigma.ι_map]
  exact Category.assoc _ _ _

private theorem presentationMap_isClosedEmbedding
    [Nonempty J] (A B : J → PointedCGWH.{u, v}) (f : ∀ j, A j ⟶ B j)
    (hf : ∀ j, IsClosedEmbedding (ConcreteCategory.hom (f j).right)) :
    IsClosedEmbedding (ConcreteCategory.hom (presentationMap A B f).right) := by
  let P : CGWH.{u, v} := CGWH.point
  let C : CGWH.{u, v} := ∐ fun _ : J => P
  let _ : Nonempty C :=
    ⟨Limits.Sigma.ι (fun _ : J => P) (Classical.choice (inferInstance : Nonempty J))
      PUnit.unit⟩
  let sA := coproductBasepointMap A
  let sB := coproductBasepointMap B
  let cP : C ⟶ P := CGWH.point_isTerminal.from C
  let sumMap := Limits.Sigma.map (fun j => (f j).right)
  let qA := pushout.inl sA cP
  let qB := pushout.inl sB cP
  let g := (presentationMap A B f).right
  have hsA : IsClosedEmbedding (ConcreteCategory.hom sA) :=
    basepointMap_isClosedEmbedding A
  have hsB : IsClosedEmbedding (ConcreteCategory.hom sB) :=
    basepointMap_isClosedEmbedding B
  have hSum : IsClosedEmbedding (ConcreteCategory.hom sumMap) := by
    change (TopCat.closedEmbeddings.inverseImage CGWH.cgwhToTop) sumMap
    apply MorphismProperty.colimMap
    rintro ⟨j⟩
    exact hf j
  have hReflect : sumMap ⁻¹' Set.range sB = Set.range sA := by
    ext x
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, hSum.injective ?_⟩
      have hn := ConcreteCategory.congr_hom (basepointMap_natural A B f) z
      exact hn.trans hz
    · rintro ⟨z, rfl⟩
      refine ⟨z, ?_⟩
      exact (ConcreteCategory.congr_hom (basepointMap_natural A B f) z).symm
  apply Topology.isClosedEmbedding_of_single_class_quotients
    sumMap qA qB g
    (CGWH.isQuotientMap_pointPushout_inl sA hsA)
    (CGWH.isQuotientMap_pointPushout_inl sB hsB)
    (Set.range sA) (Set.range sB)
    (nativePointPushout_kernel sA hsA)
    (nativePointPushout_kernel sB hsB)
    hsB.isClosed_range hReflect
  · intro x
    have hSquare : qA ≫ g = sumMap ≫ qB := by
      dsimp only [qA, g, presentationMap]
      exact pushout.inl_desc _ _ _
    exact ConcreteCategory.congr_hom hSquare x
  · exact hSum
  · exact (ConcreteCategory.hom g).continuous

/-- The actual pointed empty coproduct has the original native point as its underlying carrier. -/
def coproductEmptyIso (X : J → PointedCGWH.{u, v}) [IsEmpty J] :
    (∐ X) ≅ Under.mk (𝟙 CGWH.point.{u, v}) :=
  colimit.isoColimitCocone
    ⟨Cofan.mk (Under.mk (𝟙 CGWH.point.{u, v})) (fun j => isEmptyElim j),
      Cofan.IsColimit.mk _ (fun s => Under.mkIdInitial.to s.pt)
        (fun _ j => isEmptyElim j)
    (fun _s m _ => Under.mkIdInitial.hom_ext m _)⟩

/-- Arbitrary component closed embeddings induce a closed embedding on the
chosen pointed coproduct. -/
theorem isClosedEmbedding_coproductMap
    (A B : J → PointedCGWH.{u, v}) (f : ∀ j, A j ⟶ B j)
    (hf : ∀ j, IsClosedEmbedding (ConcreteCategory.hom (f j).right)) :
    IsClosedEmbedding (ConcreteCategory.hom (Limits.Sigma.map f).right) := by
  classical
  by_cases hJ : Nonempty J
  · let _ : Nonempty J := hJ
    have hRaw := presentationMap_isClosedEmbedding A B f hf
    let eA := pointedToCGWH.mapIso (coproductPointIso A)
    let eB := pointedToCGWH.mapIso (coproductPointIso B)
    have hComm :
        eA.hom ≫ (presentationMap A B f).right =
          (Limits.Sigma.map f).right ≫ eB.hom :=
      congrArg (fun h => h.right) (presentationMap_natural A B f)
    have hFull : IsClosedEmbedding
        (ConcreteCategory.hom ((Limits.Sigma.map f).right ≫ eB.hom)) := by
      rw [← hComm]
      exact hRaw.comp (TopCat.homeoOfIso (CGWH.cgwhToTop.mapIso eA)).isClosedEmbedding
    exact (TopCat.closedEmbeddings.cancel_right_of_respectsIso
      (CGWH.cgwhToTop.map (Limits.Sigma.map f).right)
      (CGWH.cgwhToTop.mapIso eB).hom).mp hFull
  · let _ : IsEmpty J := not_nonempty_iff.mp hJ
    let eA := pointedToCGWH.mapIso (coproductEmptyIso A)
    let eB := pointedToCGWH.mapIso (coproductEmptyIso B)
    have hId : (Limits.Sigma.map f).right ≫ eB.hom = eA.hom := by
      have h : Limits.Sigma.map f ≫ (coproductEmptyIso B).hom =
          (coproductEmptyIso A).hom := by
        apply Limits.Sigma.hom_ext
        intro j
        exact isEmptyElim j
      exact congrArg (fun h => h.right) h
    have hFull : IsClosedEmbedding
        (ConcreteCategory.hom ((Limits.Sigma.map f).right ≫ eB.hom)) := by
      rw [hId]
      exact (TopCat.homeoOfIso (CGWH.cgwhToTop.mapIso eA)).isClosedEmbedding
    exact (TopCat.closedEmbeddings.cancel_right_of_respectsIso
      (CGWH.cgwhToTop.map (Limits.Sigma.map f).right)
      (CGWH.cgwhToTop.mapIso eB).hom).mp hFull

/-- Closedness uses both original colimit cofans and their actual induced map. -/
theorem isClosedEmbedding_cofanMap
    (A B : J → PointedCGWH.{u, v}) (f : ∀ j, A j ⟶ B j)
    (cA : Cofan A) (cB : Cofan B) (hA : IsColimit cA) (hB : IsColimit cB)
    (m : cA.pt ⟶ cB.pt) (hm : ∀ j, cA.inj j ≫ m = f j ≫ cB.inj j)
    (hf : ∀ j, IsClosedEmbedding (ConcreteCategory.hom (f j).right)) :
    IsClosedEmbedding (ConcreteCategory.hom m.right) := by
  let eA : (∐ A) ≅ cA.pt := colimit.isoColimitCocone ⟨cA, hA⟩
  let eB : (∐ B) ≅ cB.pt := colimit.isoColimitCocone ⟨cB, hB⟩
  have heA (j : J) : Limits.Sigma.ι A j ≫ eA.hom = cA.inj j :=
    colimit.isoColimitCocone_ι_hom ⟨cA, hA⟩ ⟨j⟩
  have heB (j : J) : Limits.Sigma.ι B j ≫ eB.hom = cB.inj j :=
    colimit.isoColimitCocone_ι_hom ⟨cB, hB⟩ ⟨j⟩
  have hComm : eA.hom ≫ m = Limits.Sigma.map f ≫ eB.hom := by
    apply Limits.Sigma.hom_ext
    intro j
    rw [← Category.assoc, heA, hm, ← Category.assoc,
      Limits.Sigma.ι_map, Category.assoc, heB]
  let P : MorphismProperty CGWH.{u, v} :=
    TopCat.closedEmbeddings.inverseImage CGWH.cgwhToTop
  have hRaw : P (Limits.Sigma.map f).right := isClosedEmbedding_coproductMap A B f hf
  let hArrow : Arrow.mk (Limits.Sigma.map f).right ≅ Arrow.mk m.right :=
    Arrow.isoMk (pointedToCGWH.mapIso eA) (pointedToCGWH.mapIso eB)
      (congrArg (fun h => h.right) hComm)
  exact (P.arrow_mk_iso_iff hArrow).mp hRaw


private def liftedBinaryFamily (X Y : CGWH.{u, v}) : ULift.{v} Bool → CGWH.{u, v} :=
  fun j => Bool.casesOn j.down X Y

private def liftedBinaryCofan (X Y : CGWH.{u, v}) :
    Cofan (liftedBinaryFamily X Y) :=
  Cofan.mk (X ⨿ Y) (fun j => by
    rcases j with ⟨j⟩
    cases j
    · exact coprod.inl
    · exact coprod.inr)

private def liftedBinaryCofanIsColimit (X Y : CGWH.{u, v}) :
    IsColimit (liftedBinaryCofan X Y) :=
  Cofan.IsColimit.mk _
    (fun s => coprod.desc (s.inj ⟨false⟩) (s.inj ⟨true⟩))
    (fun s j => by
      rcases j with ⟨j⟩
      cases j <;> simp [liftedBinaryCofan, liftedBinaryFamily])
    (fun s m hm => by
      let mR : X ⨿ Y ⟶ s.pt := m
      change mR = coprod.desc (s.inj ⟨false⟩) (s.inj ⟨true⟩)
      apply coprod.hom_ext
      · rw [coprod.inl_desc]
        simpa only [liftedBinaryCofan, cofan_mk_inj, liftedBinaryFamily, mR] using hm ⟨false⟩
      · rw [coprod.inr_desc]
        simpa only [liftedBinaryCofan, cofan_mk_inj, liftedBinaryFamily, mR] using hm ⟨true⟩)

/-- Freely adjoining the original selected point preserves an underlying closed embedding. -/
theorem isClosedEmbedding_costarMap
    {X Y : CGWH.{u, v}} (f : X ⟶ Y)
    (hf : IsClosedEmbedding (ConcreteCategory.hom f)) :
    IsClosedEmbedding (ConcreteCategory.hom
      ((Under.costar CGWH.point).map f).right) := by
  let P : CGWH.{u, v} := CGWH.point
  let W : MorphismProperty CGWH.{u, v} :=
    TopCat.closedEmbeddings.inverseImage CGWH.cgwhToTop
  let A := liftedBinaryFamily P X
  let B := liftedBinaryFamily P Y
  let φ : Discrete.functor A ⟶ Discrete.functor B :=
    Discrete.natTrans (fun ⟨⟨j⟩⟩ => by
      cases j
      · exact 𝟙 P
      · exact f)
  have hφ : W.functorCategory _ φ := by
    rintro ⟨⟨j⟩⟩
    cases j
    · change IsClosedEmbedding (ConcreteCategory.hom (𝟙 P))
      exact IsClosedEmbedding.id
    · change IsClosedEmbedding (ConcreteCategory.hom f)
      exact hf
  have hMap : W (coprod.map (𝟙 P) f) := by
    apply MorphismProperty.colimitsOfShape_le
      (W := W) (J := Discrete (ULift.{v} Bool))
    exact MorphismProperty.colimitsOfShape.mk'
      (Discrete.functor A) (Discrete.functor B)
      (liftedBinaryCofan P X) (liftedBinaryCofan P Y)
      (liftedBinaryCofanIsColimit P X) (liftedBinaryCofanIsColimit P Y)
      φ hφ (coprod.map (𝟙 P) f) (by
        rintro ⟨⟨j⟩⟩
        cases j <;> simp [liftedBinaryCofan, liftedBinaryFamily, φ, A, B])
  exact hMap

end PointedCGWH

namespace CGWH

/-- The caller's exact native colimit cocone retains point representatives
from its original objects, including arbitrary original relative roots. -/
private theorem colimitPoint {J : Type wJ} [Category.{vJ} J]
    (F : J ⥤ CGWH.{u, v}) [HasColimit F]
    [HasColimit (F ⋙ CGWH.cgwhToCompactlyGenerated)]
    (s : Cocone F) (hs : IsColimit s) (z : ↥s.pt) :
    ∃ (j : J) (x : ↥(F.obj j)), s.ι.app j x = z := by
  let e := (colimit.isColimit F).coconePointUniqueUpToIso hs
  obtain ⟨j, x, hx⟩ := CGWH.colimit_exists_rep F (e.inv z)
  refine ⟨j, x, ?_⟩
  have he := ConcreteCategory.congr_hom
    (IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) hs j) x
  change e.hom (colimit.ι F j x) = s.ι.app j x at he
  rw [← he, hx]
  simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
    ConcreteCategory.congr_hom e.inv_hom_id z

/-- Every point in an actual native pushout is represented by one of its
two original endpoint inclusions. -/
private theorem pushoutPoint {A B C D : CGWH.{u, v}}
    (f : A ⟶ B) (g : A ⟶ C) (l : B ⟶ D) (r : C ⟶ D)
    (sq : IsPushout f g l r) (z : ↥D) :
    (∃ x : ↥B, l x = z) ∨ ∃ y : ↥C, r y = z := by
  obtain ⟨j, x, hx⟩ := colimitPoint (span f g) sq.cocone sq.isColimit z
  cases j with
  | none => exact Or.inl ⟨f x, hx⟩
  | some j =>
    cases j with
    | left => exact Or.inl ⟨x, hx⟩
    | right => exact Or.inr ⟨x, hx⟩

end CGWH

namespace PointedCGWH

/-- Every point of the caller's connected colimit cocone is represented
by one of the original pointed objects and its actual endpoint map. -/
theorem exists_rep_of_isColimit {J : Type v} [Category.{v} J] [IsConnected J]
    (F : J ⥤ PointedCGWH.{u, v}) (s : Cocone F) (hs : IsColimit s)
    (z : ↥s.pt.right) :
    ∃ (j : J) (x : ↥(F.obj j).right), (s.ι.app j).right x = z := by
  let U := pointedToCGWH.{u, v}
  have hsU : IsColimit (U.mapCocone s) := isColimitOfPreserves U hs
  exact CGWH.colimitPoint (F ⋙ U) (U.mapCocone s) hsU z

/-- Each point of the original pointed pushout has a representative in
one of its two actual endpoint inclusions. -/
theorem exists_rep_of_isPushout {A B C D : PointedCGWH.{u, v}}
    (f : A ⟶ B) (g : A ⟶ C) (l : B ⟶ D) (r : C ⟶ D)
    (sq : IsPushout f g l r) (z : ↥D.right) :
    (∃ x : ↥B.right, l.right x = z) ∨ ∃ y : ↥C.right, r.right y = z :=
  CGWH.pushoutPoint f.right g.right l.right r.right (sq.map pointedToCGWH) z

end PointedCGWH

namespace PointedCGWH

/-- Point coverage of the actual pointed cofan includes its shared native
point. In particular it remains valid for the original empty family. -/
theorem cofanPoint {J : Type v} (X : J → PointedCGWH.{u, v})
    (s : Cofan X) (hs : IsColimit s) (z : ↥s.pt.right) :
    z = s.pt.hom PUnit.unit ∨
      ∃ (j : J) (x : ↥(X j).right), (s.inj j).right x = z := by
  let p := coproductPointCofan X
  let hp := coproductPointCofanIsColimit X
  let e : p.pt ≅ s.pt := hp.coconePointUniqueUpToIso hs
  let b := coproductBasepointMap X
  let q := CGWH.point_isTerminal.from (∐ fun _ : J => CGWH.point.{u, v})
  let z' : ↥p.pt.right := e.inv.right z
  have he : e.hom.right z' = z := by
    simpa only [Under.comp_right, Under.id_right, ConcreteCategory.comp_apply,
      ConcreteCategory.id_apply] using
      ConcreteCategory.congr_hom
        (congrArg (fun m : s.pt ⟶ s.pt => m.right) e.inv_hom_id) z
  obtain hleft | hright := CGWH.pushoutPoint b q _ _
    (IsPushout.of_hasPushout b q) z'
  · obtain ⟨x, hx⟩ := hleft
    let F := Discrete.functor (fun j : J => (X j).right)
    obtain ⟨⟨j⟩, y, hy⟩ := CGWH.colimitPoint F
      (colimit.cocone F) (colimit.isColimit F) x
    change Limits.Sigma.ι (fun j : J => (X j).right) j y = x at hy
    have hleg : (coproductPointInjection X j) ≫ e.hom = s.inj j :=
      hp.comp_coconePointUniqueUpToIso_hom hs ⟨j⟩
    right
    refine ⟨j, y, ?_⟩
    calc
      (s.inj j).right y = e.hom.right ((coproductPointInjection X j).right y) :=
        (ConcreteCategory.congr_hom
          (congrArg (fun m : X j ⟶ s.pt => m.right) hleg) y).symm
      _ = e.hom.right z' := by
        change e.hom.right (pushout.inl b q (Limits.Sigma.ι (fun j : J => (X j).right) j y)) = _
        rw [hy, hx]
      _ = z := he
  · obtain ⟨x, hx⟩ := hright
    left
    calc
      z = e.hom.right z' := he.symm
      _ = e.hom.right (p.pt.hom PUnit.unit) := by
        rw [← hx]
        congr 2
      _ = s.pt.hom PUnit.unit := ConcreteCategory.congr_hom e.hom.w PUnit.unit

end PointedCGWH
