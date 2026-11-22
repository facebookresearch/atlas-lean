/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- The original power at outer zero and its inner mapping end.
import MathlibExt.AlgebraicTopology.SimplicialSpace.FullEEquivalenceEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSpace.WalkingEUnitDwyerKan
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# The whole chosen power at outer zero and the original inner mapping end

The left adjunction is constructed from the actual initial object [0] of the
opposite simplex category. Native right-adjoint uniqueness then gives the
comparison for EVERY original scalar. Its constant-map law is checked through
the actual representable Yoneda projection and the original full-E collapse.
No vertex-only comparison or caller-supplied Iso is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory
open scoped Simplicial MonoidalCategory SimplicialSpace.Inner SimplicialSpace.Cartesian

namespace SimplicialSpace.WholePowerZeroOriginalMappingIso

/-- The original constant OUTER diagram, retaining the entire inner scalar. -/
def outerConst : SSet.{u} ⥤ SimplicialSpace.{u} :=
  (Functor.const SimplexCategoryᵒᵖ) ⋙ ofSimplicialObject

/-- Evaluate the original outer zero row without changing the inner scalar. -/
def outerZero : SimplicialSpace.{u} ⥤ SSet.{u} :=
  forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet.{u}).obj (op ⦋0⦌)

/-- Every zero-row map extends along the actual original operator to zero. -/
def outerZeroArrow {K : SSet.{u}} (W : SimplicialSpace.{u})
    (g : K ⟶ W.diagram _⦋0⦌) : outerConst.obj K ⟶ W :=
  InducedCategory.homMk
    { app := fun m => g ≫ W.diagram.map (SimplexCategory.const m.unop ⦋0⦌ 0).op
      naturality := by
        intro m n δ
        have hδ : (SimplexCategory.const m.unop ⦋0⦌ 0).op ≫ δ =
            (SimplexCategory.const n.unop ⦋0⦌ 0).op := by
          simpa only [op_comp, Quiver.Hom.op_unop] using
            congrArg (fun f : n.unop ⟶ ⦋0⦌ => f.op)
              (SimplexCategory.eq_const_to_zero
                (δ.unop ≫ SimplexCategory.const m.unop ⦋0⦌ 0))
        change g ≫ W.diagram.map (SimplexCategory.const n.unop ⦋0⦌ 0).op =
          (g ≫ W.diagram.map (SimplexCategory.const m.unop ⦋0⦌ 0).op) ≫
            W.diagram.map δ
        rw [Category.assoc, ← W.diagram.map_comp, hδ] }

/-- Evaluation back at zero is exactly the original map. -/
theorem outerZeroArrow_zero {K : SSet.{u}} (W : SimplicialSpace.{u})
    (g : K ⟶ W.diagram _⦋0⦌) :
    (outerZeroArrow W g).hom.app (op ⦋0⦌) = g := by
  change g ≫ W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op = g
  rw [(SimplexCategory.eq_const_to_zero (𝟙 ⦋0⦌)).symm,
    op_id, W.diagram.map_id, Category.comp_id]

/-- The entire natural transformation is determined by its original zero row. -/
def outerZeroHomEquiv (K : SSet.{u}) (W : SimplicialSpace.{u}) :
    (outerConst.obj K ⟶ W) ≃ (K ⟶ outerZero.obj W) where
  toFun f := f.hom.app (op ⦋0⦌)
  invFun g := outerZeroArrow W g
  left_inv f := by
    apply SimplicialSpace.homEquiv.injective
    apply NatTrans.ext
    funext m
    have h := f.hom.naturality (SimplexCategory.const m.unop ⦋0⦌ 0).op
    change (𝟙 K) ≫ f.hom.app m =
      f.hom.app (op ⦋0⦌) ≫ W.diagram.map
        (SimplexCategory.const m.unop ⦋0⦌ 0).op at h
    change f.hom.app (op ⦋0⦌) ≫ W.diagram.map
      (SimplexCategory.const m.unop ⦋0⦌ 0).op = f.hom.app m
    exact h.symm.trans (Category.id_comp (f.hom.app m))
  right_inv g := outerZeroArrow_zero W g

/-- This is the genuine constant-outer/evaluation adjunction at [0]. -/
def outerConstAdjunction : outerConst.{u} ⊣ outerZero.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := outerZeroHomEquiv
      homEquiv_naturality_left_symm := by
        intro K L W k g
        apply SimplicialSpace.homEquiv.injective
        apply NatTrans.ext
        funext m
        change (k ≫ g) ≫ W.diagram.map
            (SimplexCategory.const m.unop ⦋0⦌ 0).op =
          k ≫ (g ≫ W.diagram.map (SimplexCategory.const m.unop ⦋0⦌ 0).op)
        exact Category.assoc _ _ _
      homEquiv_naturality_right := by intro K W V f g; rfl }

/-- The native whole Cartesian tensor with the constant outer scalar IS the
original inner tensor, with the same pair in every bidegree. -/
def tensorConstIso (A : SimplicialSpace.{u}) :
    outerConst ⋙ tensorLeft A ≅ innerTensorBifunctor.obj A :=
  NatIso.ofComponents (fun _ => InducedCategory.isoMk (Iso.refl _)) (by
    intro K L k
    apply SimplicialSpace.homEquiv.injective
    apply NatTrans.ext
    funext m
    rfl)

/-- Both native adjunctions have the SAME original inner tensor left functor. -/
def powerZeroScalarAdjunction (A : SimplicialSpace.{u}) :
    innerTensorBifunctor.obj A ⊣ ihom A ⋙ outerZero :=
  (outerConstAdjunction.comp (ihom.adjunction A)).ofNatIsoLeft (tensorConstIso A)

/-- Native right-adjoint uniqueness constructs the full target-natural Iso. -/
def powerZeroScalarNatIso (A : SimplicialSpace.{u}) :
    ihom A ⋙ outerZero ≅ innerHomFunctor.obj (op A) :=
  (powerZeroScalarAdjunction A).rightAdjointUniq (innerTensorHomAdjunction₂.adj A)

/-- The chosen whole exponential at zero is the actual original scalar end. -/
def powerZeroScalarIso (A W : SimplicialSpace.{u}) :
    ((ihom A).obj W).diagram _⦋0⦌ ≅ (innerHomFunctor.obj (op A)).obj W :=
  (powerZeroScalarNatIso A).app W

private theorem scalarAdjunction_homEquiv (A : SimplicialSpace.{u}) :
    (innerTensorHomAdjunction₂.adj A).homEquiv =
      fun K W => innerTensorHomEquiv K A W := by
  change (Adjunction.mkOfHomEquiv _).homEquiv = _
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- For EVERY scalar K both original tensor transposes are the same map. -/
theorem powerZeroScalarIso_characteristic (A : SimplicialSpace.{u})
    (K : SSet.{u}) (W : SimplicialSpace.{u})
    (f : (innerTensor K).obj A ⟶ W) :
    (powerZeroScalarAdjunction A).homEquiv K W f ≫
        (powerZeroScalarIso A W).hom = innerTensorHomEquiv K A W f := by
  have h : (powerZeroScalarAdjunction A).homEquiv K W f ≫
      ((powerZeroScalarAdjunction A).rightAdjointUniq
        (innerTensorHomAdjunction₂.adj A)).hom.app W =
      (innerTensorHomAdjunction₂.adj A).homEquiv K W f := by
    rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, Category.assoc,
      (((powerZeroScalarAdjunction A).rightAdjointUniq
        (innerTensorHomAdjunction₂.adj A)).hom.naturality f),
      ← Category.assoc, Adjunction.unit_rightAdjointUniq_hom_app]
  exact h.trans (congrArg (fun e => e K W f) (scalarAdjunction_homEquiv A))

/-- Every actual target map commutes with this same complete mapping Iso. -/
theorem powerZeroScalarIso_target {A W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    ((ihom A).map f).hom.app (op ⦋0⦌) ≫ (powerZeroScalarIso A V).hom =
      (powerZeroScalarIso A W).hom ≫ (innerHomFunctor.obj (op A)).map f :=
  (powerZeroScalarNatIso A).hom.naturality f

/-- The original zero-representable tensor map sends every inner scalar along
the actual outer collapse, without selecting an unrelated vertex. -/
def zeroRepresentableTensorMap (W : SimplicialSpace.{u}) :
    (innerTensor (W.diagram _⦋0⦌)).obj
        (discreteInnerFunctor.obj (Δ[0] : SSet.{u})) ⟶ W :=
  InducedCategory.homMk
    { app := fun m => CartesianMonoidalCategory.snd
        ((discreteInnerFunctor.obj (Δ[0] : SSet.{u})).diagram.obj m)
          (W.diagram _⦋0⦌) ≫
        W.diagram.map (SimplexCategory.const m.unop ⦋0⦌ 0).op
      naturality := by
        intro m n δ
        have hδ : (SimplexCategory.const m.unop ⦋0⦌ 0).op ≫ δ =
            (SimplexCategory.const n.unop ⦋0⦌ 0).op := by
          simpa only [op_comp, Quiver.Hom.op_unop] using
            congrArg (fun f : n.unop ⟶ ⦋0⦌ => f.op)
              (SimplexCategory.eq_const_to_zero
                (δ.unop ≫ SimplexCategory.const m.unop ⦋0⦌ 0))
        change (_ ▷ W.diagram _⦋0⦌) ≫
            (CartesianMonoidalCategory.snd _ _ ≫ W.diagram.map
              (SimplexCategory.const n.unop ⦋0⦌ 0).op) =
          (CartesianMonoidalCategory.snd _ _ ≫ W.diagram.map
            (SimplexCategory.const m.unop ⦋0⦌ 0).op) ≫ W.diagram.map δ
        rw [← Category.assoc, whiskerRight_snd, Category.assoc,
          ← W.diagram.map_comp, hδ] }

/-- The actual enriched Yoneda inverse follows from its PUBLIC original
identity-simplex projection and the universal inner tensor representation. -/
private theorem curry_evaluatePoint {A B K : SSet.{u}}
    (p : 𝟙_ SSet.{u} ⟶ A) (f : A ⊗ K ⟶ B) :
    curry f ≫ ((λ_ _).inv ≫ p ▷ _ ≫ (ihom.ev A).app B) =
      (λ_ K).inv ≫ p ▷ K ≫ f := by
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    whiskerLeft_curry_ihom_ev_app]

theorem zeroRepresentableTensorMap_yoneda (W : SimplicialSpace.{u}) :
    innerTensorHomEquiv (W.diagram _⦋0⦌)
        (discreteInnerFunctor.obj (Δ[0] : SSet.{u})) W
        (zeroRepresentableTensorMap W) = (discreteYonedaIso W 0).inv := by
  apply (cancel_mono (discreteYonedaIso W 0).hom).mp
  rw [Iso.inv_hom_id]
  have hy : (discreteYonedaIso W 0).hom =
      innerHomπ (discreteInnerFunctor.obj (Δ[0] : SSet.{u})) W (op ⦋0⦌) ≫
        (λ_ _).inv ≫ SSet.Rezk.representableIdentityPoint 0 ▷ _ ≫
          (ihom.ev _).app (W.diagram _⦋0⦌) :=
    SSet.Rezk.pointwiseYonedaIso_hom_projection 0 W.diagram
  let X := discreteInnerFunctor.obj (Δ[0] : SSet.{u})
  let q := innerTensorHomEquiv (W.diagram _⦋0⦌) X W (zeroRepresentableTensorMap W)
  let ev : (ihom (X.diagram _⦋0⦌)).obj (W.diagram _⦋0⦌) ⟶ W.diagram _⦋0⦌ :=
    (λ_ _).inv ≫ SSet.Rezk.representableIdentityPoint 0 ▷ _ ≫ (ihom.ev _).app _
  have he : q ≫ (discreteYonedaIso W 0).hom =
      (q ≫ innerHomπ X W (op ⦋0⦌)) ≫ ev :=
    (congrArg (fun g => q ≫ g) hy).trans (Category.assoc _ _ _).symm
  have hp := innerTensorHomEquiv_π (W.diagram _⦋0⦌) X W
    (zeroRepresentableTensorMap W) (op ⦋0⦌)
  have hcalc := curry_evaluatePoint
    (show 𝟙_ SSet.{u} ⟶ X.diagram _⦋0⦌ from SSet.Rezk.representableIdentityPoint 0)
    (tensorComponent (W.diagram _⦋0⦌) X W (zeroRepresentableTensorMap W) (op ⦋0⦌))
  refine he.trans ((congrArg (fun g => g ≫ ev) hp).trans (hcalc.trans ?_))
  change (λ_ (W.diagram _⦋0⦌)).inv ≫
      SSet.Rezk.representableIdentityPoint 0 ▷ (W.diagram _⦋0⦌) ≫
      CartesianMonoidalCategory.snd _ _ ≫ W.diagram.map
        (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op = _
  rw [whiskerRight_snd_assoc, leftUnitor_inv_snd_assoc,
    (SimplexCategory.eq_const_to_zero (𝟙 ⦋0⦌)).symm, op_id,
    W.diagram.map_id]

/-- The original whole E constant tensor map, before ANY transpose. -/
def fullEInnerConstantMap (W : SimplicialSpace.{u}) :
    (innerTensor (W.diagram _⦋0⦌)).obj WalkingEUnit.coherentSpace ⟶ W :=
  (tensorConstIso WalkingEUnit.coherentSpace).inv.app (W.diagram _⦋0⦌) ≫
    CartesianMonoidalCategory.snd WalkingEUnit.coherentSpace
      (outerConst.obj (W.diagram _⦋0⦌)) ≫ outerZeroArrow W (𝟙 _)

/-- Its enriched transpose IS the original full-E constant map, via the
same actual E→Δ[0] collapse and the complete Yoneda inverse. -/
theorem fullEInnerConstantMap_enriched (W : SimplicialSpace.{u}) :
    innerTensorHomEquiv (W.diagram _⦋0⦌) WalkingEUnit.coherentSpace W
      (fullEInnerConstantMap W) = FullEEquivalence.constantMap W := by
  let ε := ofSimplicialObject.map SSet.Rezk.FiniteCompleteness.epsilon
  have h := innerTensorHomEquiv_source ε (W.diagram _⦋0⦌) W
    (zeroRepresentableTensorMap W)
  change innerTensorHomEquiv (W.diagram _⦋0⦌) WalkingEUnit.coherentSpace W
      ((innerTensor (W.diagram _⦋0⦌)).map ε ≫ zeroRepresentableTensorMap W) =
    innerTensorHomEquiv (W.diagram _⦋0⦌)
      (discreteInnerFunctor.obj (Δ[0] : SSet.{u})) W
      (zeroRepresentableTensorMap W) ≫ (innerHomFunctor.map ε.op).app W at h
  rw [zeroRepresentableTensorMap_yoneda] at h
  change innerTensorHomEquiv (W.diagram _⦋0⦌) WalkingEUnit.coherentSpace W
      ((innerTensor (W.diagram _⦋0⦌)).map ε ≫ zeroRepresentableTensorMap W) =
    FullEEquivalence.constantMap W at h
  have hf : fullEInnerConstantMap W =
      (innerTensor (W.diagram _⦋0⦌)).map ε ≫ zeroRepresentableTensorMap W := by
    apply SimplicialSpace.homEquiv.injective
    apply NatTrans.ext
    funext m
    change CartesianMonoidalCategory.snd _ _ ≫ W.diagram.map
        (SimplexCategory.const m.unop ⦋0⦌ 0).op =
      (ε.hom.app m ▷ W.diagram _⦋0⦌) ≫
        (CartesianMonoidalCategory.snd _ _ ≫ W.diagram.map
          (SimplexCategory.const m.unop ⦋0⦌ 0).op)
    rw [← Category.assoc, whiskerRight_snd]
  rw [hf]
  exact h

/-- The comparison sends the SAME native curry-of-second-projection constant
power to the original complete full-E constant map. -/
theorem powerZeroScalarIso_constantPower (W : SimplicialSpace.{u}) :
    (WalkingEUnit.constantPower W).hom.app (op ⦋0⦌) ≫
        (powerZeroScalarIso WalkingEUnit.coherentSpace W).hom =
      FullEEquivalence.constantMap W := by
  have h := powerZeroScalarIso_characteristic WalkingEUnit.coherentSpace
    (W.diagram _⦋0⦌) W (fullEInnerConstantMap W)
  have h₀ : (powerZeroScalarAdjunction WalkingEUnit.coherentSpace).homEquiv
      (W.diagram _⦋0⦌) W (fullEInnerConstantMap W) =
        (WalkingEUnit.constantPower W).hom.app (op ⦋0⦌) := by
    rw [powerZeroScalarAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply,
      Adjunction.comp_homEquiv]
    change (curry ((tensorConstIso WalkingEUnit.coherentSpace).hom.app
        (W.diagram _⦋0⦌) ≫ fullEInnerConstantMap W)).hom.app (op ⦋0⦌) = _
    have ht : (tensorConstIso WalkingEUnit.coherentSpace).hom.app
        (W.diagram _⦋0⦌) ≫ fullEInnerConstantMap W =
      CartesianMonoidalCategory.snd WalkingEUnit.coherentSpace
        (outerConst.obj (W.diagram _⦋0⦌)) ≫ outerZeroArrow W (𝟙 _) := by
      unfold fullEInnerConstantMap
      exact Iso.hom_inv_id_assoc ((tensorConstIso WalkingEUnit.coherentSpace).app
        (W.diagram _⦋0⦌)) _
    rw [ht, ← whiskerLeft_snd, curry_natural_left]
    change (outerZeroArrow W (𝟙 _)).hom.app (op ⦋0⦌) ≫
      (WalkingEUnit.constantPower W).hom.app (op ⦋0⦌) = _
    rw [outerZeroArrow_zero]
    exact Category.id_comp _
  rw [h₀, fullEInnerConstantMap_enriched] at h
  exact h

end SimplicialSpace.WholePowerZeroOriginalMappingIso
