/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.Smash
public import MathlibExt.Topology.Category.CGWH.ClosedEmbeddingProduct
public import MathlibExt.Topology.Category.CGWH.PointPushout
public import MathlibExt.Topology.Maps.CollapsedAxes

/-!
# Closed embeddings and the native smash quotient

The wedge is exactly the union of the two basepoint faces of the selected
Cartesian product. The native smash projection carries the quotient topology.
These descriptions retain the actual selected product and pushout maps.
Closed embeddings reflect those faces, so they descend through the smash
quotient to closed embeddings. Tensoring with an arbitrary pointed factor
therefore preserves closed embeddings.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory Topology

namespace PointedCGWH

private theorem point_closedEmbedding (X : PointedCGWH.{u, v}) :
    IsClosedEmbedding (ConcreteCategory.hom X.hom) := by
  let _ : Subsingleton CGWH.point.{u, v} := by
    change Subsingleton PUnit.{v + 1}
    infer_instance
  exact ⟨IsEmbedding.of_subsingleton _, (Set.finite_range _).isClosed⟩

/-- The wedge image consists exactly of the two native basepoint faces. -/
theorem wedgeToProduct_mem_range_iff (X Y : PointedCGWH.{u, v})
    (z : (X.right ⊗ Y.right : CGWH.{u, v})) :
    z ∈ Set.range (ConcreteCategory.hom
      (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal X Y).1.right) ↔
      CartesianMonoidalCategory.fst X.right Y.right z = X.hom PUnit.unit ∨
        CartesianMonoidalCategory.snd X.right Y.right z = Y.hom PUnit.unit := by
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal X Y
  let E := CGWH.tensorEquivProd X.right Y.right
  have hLeft (x : X.right) :
      E (p.1.right (pushout.inl X.hom Y.hom x)) = (x, Y.hom PUnit.unit) := by
    have hFace := ConcreteCategory.congr_hom
      (CategoryTheory.Pointed.smashPresentation_wedge_inl
        CGWH.point CGWH.point_isTerminal X Y) x
    change p.1.right (pushout.inl X.hom Y.hom x) =
      (CartesianMonoidalCategory.lift (𝟙 X.right)
        (CGWH.point_isTerminal.from X.right ≫ Y.hom)) x at hFace
    rw [hFace]
    apply Prod.ext
    · exact ConcreteCategory.congr_hom
        (CartesianMonoidalCategory.lift_fst (𝟙 X.right)
          (CGWH.point_isTerminal.from X.right ≫ Y.hom)) x
    · have h := ConcreteCategory.congr_hom
        (CartesianMonoidalCategory.lift_snd (𝟙 X.right)
          (CGWH.point_isTerminal.from X.right ≫ Y.hom)) x
      change _ = Y.hom PUnit.unit
      exact h.trans (congrArg (fun a => Y.hom a)
        (@Subsingleton.elim PUnit.{v + 1} inferInstance _ _))
  have hRight (y : Y.right) :
      E (p.1.right (pushout.inr X.hom Y.hom y)) = (X.hom PUnit.unit, y) := by
    have hFace := ConcreteCategory.congr_hom
      (CategoryTheory.Pointed.smashPresentation_wedge_inr
        CGWH.point CGWH.point_isTerminal X Y) y
    change p.1.right (pushout.inr X.hom Y.hom y) =
      (CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right)) y at hFace
    rw [hFace]
    apply Prod.ext
    · have h := ConcreteCategory.congr_hom
        (CartesianMonoidalCategory.lift_fst
          (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right)) y
      change _ = X.hom PUnit.unit
      exact h.trans (congrArg (fun a => X.hom a)
        (@Subsingleton.elim PUnit.{v + 1} inferInstance _ _))
    · exact ConcreteCategory.congr_hom
        (CartesianMonoidalCategory.lift_snd
          (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right)) y
  constructor
  · rintro ⟨w, rfl⟩
    have hx : IsClosedEmbedding
        (ConcreteCategory.hom (CGWH.cgwhToTop.map X.hom)) :=
      point_closedEmbedding X
    let e := CGWH.pushoutClosedComparisonIso X.hom Y.hom hx
    let w0 := (TopCat.homeoOfIso e).symm w
    have hw : (TopCat.homeoOfIso e) w0 = w :=
      (TopCat.homeoOfIso e).apply_symm_apply w
    let sq := (IsPushout.of_hasPushout
      (CGWH.cgwhToTop.map X.hom) (CGWH.cgwhToTop.map Y.hom)).map
        (forget TopCat)
    rcases CategoryTheory.Limits.Types.eq_or_eq_of_isPushout sq w0 with
      ⟨x, hx0⟩ | ⟨y, hy0⟩
    · have he := ConcreteCategory.congr_hom
        (CGWH.pushoutClosedComparisonIso_hom_inl X.hom Y.hom hx) x
      have hw' : pushout.inl X.hom Y.hom x = w :=
        he.symm.trans ((congrArg (ConcreteCategory.hom e.hom) hx0).trans hw)
      right
      rw [← hw']
      exact congrArg Prod.snd (hLeft x)
    · have he := ConcreteCategory.congr_hom
        (CGWH.pushoutClosedComparisonIso_hom_inr X.hom Y.hom hx) y
      have hw' : pushout.inr X.hom Y.hom y = w :=
        he.symm.trans ((congrArg (ConcreteCategory.hom e.hom) hy0).trans hw)
      left
      rw [← hw']
      exact congrArg Prod.fst (hRight y)
  · rintro (hz | hz)
    · refine ⟨pushout.inr X.hom Y.hom
        (CartesianMonoidalCategory.snd X.right Y.right z), ?_⟩
      apply E.injective
      rw [hRight]
      apply Prod.ext
      · exact hz.symm
      · rfl
    · refine ⟨pushout.inl X.hom Y.hom
        (CartesianMonoidalCategory.fst X.right Y.right z), ?_⟩
      apply E.injective
      rw [hLeft]
      apply Prod.ext
      · rfl
      · exact hz.symm

/-- The actual native smash projection has the quotient topology. -/
theorem smashQuotient_isQuotientMap (X Y : PointedCGWH.{u, v}) :
    IsQuotientMap (ConcreteCategory.hom
      (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal X Y).2.1.inl) := by
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal X Y
  let _ : Nonempty (((wedge).obj X).obj Y).right :=
    ⟨pushout.inl X.hom Y.hom (X.hom PUnit.unit)⟩
  exact CGWH.isQuotientMap_pointPushout_inl p.1.right
    (wedgeToProduct_isClosedEmbedding X Y)

/-- The actual native smash of two pointed closed embeddings is a closed
embedding. -/
theorem isClosedEmbedding_tensorHom
    {A B X Y : PointedCGWH.{u, v}} (f : A ⟶ B) (g : X ⟶ Y)
    (hf : IsClosedEmbedding (ConcreteCategory.hom f.right))
    (hg : IsClosedEmbedding (ConcreteCategory.hom g.right)) :
    IsClosedEmbedding (ConcreteCategory.hom (f ⊗ₘ g).right) := by
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let pA := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal A X
  let pB := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal B Y
  let CA : Set (A.right ⊗ X.right : CGWH.{u, v}) :=
    Set.range (ConcreteCategory.hom pA.1.right)
  let CB : Set (B.right ⊗ Y.right : CGWH.{u, v}) :=
    Set.range (ConcreteCategory.hom pB.1.right)
  let qA : A.right ⊗ X.right ⟶ pA.2.1.pt := pA.2.1.inl
  let qB : B.right ⊗ Y.right ⟶ pB.2.1.pt := pB.2.1.inl
  have hKernelA (a b : (A.right ⊗ X.right : CGWH.{u, v})) :
      qA a = qA b ↔ a = b ∨ (a ∈ CA ∧ b ∈ CA) :=
    smashQuotient_eq_iff A X a b
  have hKernelB (a b : (B.right ⊗ Y.right : CGWH.{u, v})) :
      qB a = qB b ↔ a = b ∨ (a ∈ CB ∧ b ∈ CB) :=
    smashQuotient_eq_iff B Y a b
  have hClosedB : IsClosed CB :=
    (wedgeToProduct_isClosedEmbedding B Y).isClosed_range
  have hReflect :
      (ConcreteCategory.hom (f.right ⊗ₘ g.right)) ⁻¹' CB = CA := by
    ext z
    change (f.right ⊗ₘ g.right) z ∈ CB ↔ z ∈ CA
    rw [wedgeToProduct_mem_range_iff, wedgeToProduct_mem_range_iff]
    have hF : f.right (A.hom PUnit.unit) = B.hom PUnit.unit :=
      ConcreteCategory.congr_hom (Under.w f) PUnit.unit
    have hG : g.right (X.hom PUnit.unit) = Y.hom PUnit.unit :=
      ConcreteCategory.congr_hom (Under.w g) PUnit.unit
    have hFst := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.tensorHom_fst f.right g.right) z
    have hSnd := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.tensorHom_snd f.right g.right) z
    change CartesianMonoidalCategory.fst B.right Y.right
        ((f.right ⊗ₘ g.right) z) =
      f.right (CartesianMonoidalCategory.fst A.right X.right z) at hFst
    change CartesianMonoidalCategory.snd B.right Y.right
        ((f.right ⊗ₘ g.right) z) =
      g.right (CartesianMonoidalCategory.snd A.right X.right z) at hSnd
    constructor
    · rintro (hz | hz)
      · exact Or.inl (hf.injective ((hFst.symm.trans hz).trans hF.symm))
      · exact Or.inr (hg.injective ((hSnd.symm.trans hz).trans hG.symm))
    · rintro (hz | hz)
      · exact Or.inl (hFst.trans ((congrArg (fun a => f.right a) hz).trans hF))
      · exact Or.inr (hSnd.trans ((congrArg (fun a => g.right a) hz).trans hG))
  have hSquare : qA ≫ (f ⊗ₘ g).right = (f.right ⊗ₘ g.right) ≫ qB :=
    CategoryTheory.Pointed.smashQuotient_naturality
      CGWH.point CGWH.point_isTerminal f g
  exact Topology.isClosedEmbedding_of_single_class_quotients
    (ConcreteCategory.hom (f.right ⊗ₘ g.right))
    (ConcreteCategory.hom qA) (ConcreteCategory.hom qB)
    (ConcreteCategory.hom (f ⊗ₘ g).right)
    (smashQuotient_isQuotientMap A X) (smashQuotient_isQuotientMap B Y)
    CA CB hKernelA hKernelB hClosedB hReflect
    (fun a => ConcreteCategory.congr_hom hSquare a)
    (CGWH.isClosedEmbedding_prodMap f.right g.right hf hg)
    (ConcreteCategory.hom (f ⊗ₘ g).right).continuous

/-- Right smash by an arbitrary pointed factor preserves closed embeddings. -/
theorem isClosedEmbedding_whiskerRight
    {A B : PointedCGWH.{u, v}} (f : A ⟶ B) (K : PointedCGWH.{u, v})
    (hf : IsClosedEmbedding (ConcreteCategory.hom f.right)) :
    IsClosedEmbedding (ConcreteCategory.hom (f ▷ K).right) := by
  simpa only [tensorHom_id] using
    isClosedEmbedding_tensorHom f (𝟙 K) hf (.id)

/-- Left smash by an arbitrary pointed factor preserves closed embeddings. -/
theorem isClosedEmbedding_whiskerLeft
    (K : PointedCGWH.{u, v}) {A B : PointedCGWH.{u, v}} (f : A ⟶ B)
    (hf : IsClosedEmbedding (ConcreteCategory.hom f.right)) :
    IsClosedEmbedding (ConcreteCategory.hom (K ◁ f).right) := by
  simpa only [id_tensorHom] using
    isClosedEmbedding_tensorHom (𝟙 K) f (.id) hf

end PointedCGWH
