/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Original Section14 raw diagonal construction, no completion outcome assumed.
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalExponentClosure
import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidSimplex
import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialDiagonal
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Functor.Currying
import MathlibExt.AlgebraicTopology.SimplicialSpace.WalkingEUnitDwyerKan

/-!
# Raw diagonals of groupoid-simplex powers

The full free-groupoid simplex coefficient defines a Cartesian power diagram and a raw
simplicial-space diagonal, functorial in the target space. The construction gives a natural
constant section and unit, identifies the coefficient-zero power with the original space, and
proves the unit bijective on inner vertices in every outer degree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory
open scoped Simplicial MonoidalCategory SimplicialSpace.Cartesian
namespace SimplicialSpace.RezkCompletionRaw

/-- The original covariant full-groupoid simplex coefficient, with no resized or pointwise
carrier. -/
def coefficient : SimplexCategory ⥤ SimplicialSpace.{u} :=
  SSet.FreeGroupoidSimplex.J.{u} ⋙ discreteInnerFunctor

/-- The true-power simplicial object m↦W raised to the original full E(m). -/
def powerDiagram (W : SimplicialSpace.{u}) : SimplicialObject SimplicialSpace.{u} :=
  coefficient.{u}.op ⋙ ((MonoidalClosed.internalHom (C := SimplicialSpace.{u})).flip.obj W)

/-- Every original coefficient operator is the native contravariant whole power map. -/
theorem powerDiagram_map (W : SimplicialSpace.{u}) {m n : SimplexCategoryᵒᵖ} (δ : m ⟶ n) :
    (powerDiagram W).map δ =
      (MonoidalClosed.pre (coefficient.map δ.unop)).app W := rfl

/-- Target maps use the actual native whole exponential functor in each original coefficient
degree. -/
def powerDiagramMap {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    powerDiagram W ⟶ powerDiagram V :=
  Functor.whiskerLeft coefficient.op
      ((MonoidalClosed.internalHom (C := SimplicialSpace.{u})).flip.map f)

/-- Target naturality retains every coefficient operator and the same actual powers. -/
theorem powerDiagramMap_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    {m n : SimplexCategoryᵒᵖ} (δ : m ⟶ n) :
    (powerDiagram W).map δ ≫ (powerDiagramMap f).app n =
      (powerDiagramMap f).app m ≫ (powerDiagram V).map δ :=
  (powerDiagramMap f).naturality δ

/-- The same constant section W→W raised to E(m), defined by the original second projection. -/
def constantPowerSection (W : SimplicialSpace.{u}) :
    (SimplicialObject.const SimplicialSpace).obj W ⟶ powerDiagram W where
  app m := MonoidalClosed.curry (CartesianMonoidalCategory.snd (coefficient.obj m.unop) W)
  naturality m n δ := by
    change (𝟙 W) ≫ MonoidalClosed.curry (CartesianMonoidalCategory.snd (coefficient.obj n.unop) W) =
      MonoidalClosed.curry (CartesianMonoidalCategory.snd (coefficient.obj m.unop) W) ≫
        (MonoidalClosed.pre (coefficient.map δ.unop)).app W
    rw [Category.id_comp, MonoidalClosed.curry_pre_app,
      CartesianMonoidalCategory.whiskerRight_snd]

/-- Constant-section naturality is a whole original target square, without choosing coefficient
vertices. -/
theorem constantPowerSection_target {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    (SimplicialObject.const SimplicialSpace).map f ≫ constantPowerSection V =
      constantPowerSection W ≫ powerDiagramMap f := by
  apply NatTrans.ext
  funext m
  change f ≫ MonoidalClosed.curry (CartesianMonoidalCategory.snd (coefficient.obj m.unop) V) =
    MonoidalClosed.curry (CartesianMonoidalCategory.snd (coefficient.obj m.unop) W) ≫
      (ihom (coefficient.obj m.unop)).map f
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_curry]
  exact CartesianMonoidalCategory.whiskerLeft_snd _ _

/-- For each original outer degree k retain m↦(W raised to E(m))_k as a simplicial object of
SSet. -/
def rowPowerDiagram (W : SimplicialSpace.{u}) (k : SimplexCategoryᵒᵖ) :
    SimplicialObject SSet.{u} :=
  powerDiagram W ⋙ forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet).obj k

/-- Original Section14 tilde-W, with k-row the actual diagonal in m and the inner simplex degree. -/
def rawCompletion (W : SimplicialSpace.{u}) : SimplicialSpace.{u} :=
  ofSimplicialObject.obj
    ((powerDiagram W ⋙ forget).flip ⋙ SSet.simplicialDiagonalFunctor)

/-- The original raw completion row is literally the diagonal of the same power diagram. -/
theorem rawCompletion_row (W : SimplicialSpace.{u}) (k : SimplexCategoryᵒᵖ) :
    (rawCompletion W).diagram.obj k = SSet.simplicialDiagonalFunctor.obj (rowPowerDiagram W k) :=
  rfl

/-- Original target maps are induced by the same diagonal functor on the full power maps. -/
def rawCompletionMap {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    rawCompletion W ⟶ rawCompletion V :=
  ofSimplicialObject.map
    (Functor.whiskerRight
      ((CategoryTheory.flipFunctor _ _ _).map (Functor.whiskerRight (powerDiagramMap f) forget))
      SSet.simplicialDiagonalFunctor)

/-- Each target-map component is the full original power-map diagonal. -/
theorem rawCompletionMap_row {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (k : SimplexCategoryᵒᵖ) :
    (rawCompletionMap f).hom.app k =
      SSet.simplicialDiagonalFunctor.map
        (Functor.whiskerRight (powerDiagramMap f)
          (forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet).obj k)) := rfl

private def rowSection (W : SimplicialSpace.{u}) (k : SimplexCategoryᵒᵖ) :
    (SimplicialObject.const SSet).obj (W.diagram.obj k) ⟶ rowPowerDiagram W k :=
  Functor.whiskerRight (constantPowerSection W)
    (forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet).obj k)

private theorem rowSection_outer (W : SimplicialSpace.{u})
    {k l : SimplexCategoryᵒᵖ} (δ : k ⟶ l) :
    (SimplicialObject.const SSet).map (W.diagram.map δ) ≫ rowSection W l =
      rowSection W k ≫ (powerDiagram W ⋙ forget).flip.map δ := by
  apply NatTrans.ext
  funext m
  change W.diagram.map δ ≫ ((constantPowerSection W).app m).hom.app l =
    ((constantPowerSection W).app m).hom.app k ≫
      ((powerDiagram W).obj m).diagram.map δ
  exact (((constantPowerSection W).app m).hom.naturality δ)

/-- The original W→tilde-W map uses the constant-diagonal inverse followed by the actual constant
section. -/
def rawCompletionUnit (W : SimplicialSpace.{u}) : W ⟶ rawCompletion W :=
  ofSimplicialObject.map
    { app k := (SSet.diagonalConstIso (W.diagram.obj k)).inv ≫
        SSet.simplicialDiagonalFunctor.map
          (Functor.whiskerRight (constantPowerSection W)
            (forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet).obj k))
      naturality k l δ := by
        have hconst := CategoryTheory.SimplicialObject.diagonalConstIso_naturality
          (Type u) (W.diagram.map δ)
        have hInv : W.diagram.map δ ≫ (SSet.diagonalConstIso (W.diagram.obj l)).inv =
            (SSet.diagonalConstIso (W.diagram.obj k)).inv ≫
              SSet.simplicialDiagonalFunctor.map
                ((SimplicialObject.const SSet).map (W.diagram.map δ)) := by
          change SSet.simplicialDiagonalFunctor.map
              ((SimplicialObject.const SSet).map (W.diagram.map δ)) ≫
                (SSet.diagonalConstIso (W.diagram.obj l)).hom =
            (SSet.diagonalConstIso (W.diagram.obj k)).hom ≫ W.diagram.map δ at hconst
          apply (cancel_mono (SSet.diagonalConstIso (W.diagram.obj l)).hom).1
          simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
          rw [hconst, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
        change W.diagram.map δ ≫
            ((SSet.diagonalConstIso (W.diagram.obj l)).inv ≫
              SSet.simplicialDiagonalFunctor.map (rowSection W l)) =
          ((SSet.diagonalConstIso (W.diagram.obj k)).inv ≫
              SSet.simplicialDiagonalFunctor.map (rowSection W k)) ≫
            SSet.simplicialDiagonalFunctor.map ((powerDiagram W ⋙ forget).flip.map δ)
        have hcomp : SSet.simplicialDiagonalFunctor.map
              ((SimplicialObject.const SSet).map (W.diagram.map δ)) ≫
                SSet.simplicialDiagonalFunctor.map (rowSection W l) =
            SSet.simplicialDiagonalFunctor.map (rowSection W k) ≫
              SSet.simplicialDiagonalFunctor.map ((powerDiagram W ⋙ forget).flip.map δ) := by
          ext a x
          exact congrFun (congrArg (fun η => ((η.app a).app a).hom)
            (rowSection_outer W δ)) x
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun g => g ≫ SSet.simplicialDiagonalFunctor.map (rowSection W l)) hInv).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun g => (SSet.diagonalConstIso (W.diagram.obj k)).inv ≫ g) hcomp).trans
                (Category.assoc _ _ _).symm))) }

/-- The original coaugmentation keeps every outer operator, not a chosen fixed-zero vertex. -/
theorem rawCompletionUnit_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    f ≫ rawCompletionUnit V = rawCompletionUnit W ≫ rawCompletionMap f := by
  apply SimplicialSpace.homEquiv.injective
  apply NatTrans.ext
  funext k
  have hconst := CategoryTheory.SimplicialObject.diagonalConstIso_naturality
    (Type u) (f.hom.app k)
  have hInv : f.hom.app k ≫ (SSet.diagonalConstIso (V.diagram.obj k)).inv =
      (SSet.diagonalConstIso (W.diagram.obj k)).inv ≫
        SSet.simplicialDiagonalFunctor.map
          ((SimplicialObject.const SSet).map (f.hom.app k)) := by
    change SSet.simplicialDiagonalFunctor.map
        ((SimplicialObject.const SSet).map (f.hom.app k)) ≫
          (SSet.diagonalConstIso (V.diagram.obj k)).hom =
      (SSet.diagonalConstIso (W.diagram.obj k)).hom ≫ f.hom.app k at hconst
    apply (cancel_mono (SSet.diagonalConstIso (V.diagram.obj k)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hconst, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hsection : (SimplicialObject.const SSet).map (f.hom.app k) ≫ rowSection V k =
      rowSection W k ≫ Functor.whiskerRight (powerDiagramMap f)
        (forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet).obj k) := by
    exact congrArg (fun η => Functor.whiskerRight η
      (forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet).obj k))
      (constantPowerSection_target f)
  change f.hom.app k ≫
      ((SSet.diagonalConstIso (V.diagram.obj k)).inv ≫
        SSet.simplicialDiagonalFunctor.map (rowSection V k)) =
    ((SSet.diagonalConstIso (W.diagram.obj k)).inv ≫
        SSet.simplicialDiagonalFunctor.map (rowSection W k)) ≫
      SSet.simplicialDiagonalFunctor.map
        (Functor.whiskerRight (powerDiagramMap f)
          (forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet).obj k))
  have hcomp : SSet.simplicialDiagonalFunctor.map
        ((SimplicialObject.const SSet).map (f.hom.app k)) ≫
          SSet.simplicialDiagonalFunctor.map (rowSection V k) =
      SSet.simplicialDiagonalFunctor.map (rowSection W k) ≫
        SSet.simplicialDiagonalFunctor.map
          (Functor.whiskerRight (powerDiagramMap f)
            (forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet).obj k)) := by
    ext a x
    exact congrFun (congrArg (fun η => ((η.app a).app a).hom) hsection) x
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ SSet.simplicialDiagonalFunctor.map (rowSection V k)) hInv).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun g => (SSet.diagonalConstIso (W.diagram.obj k)).inv ≫ g) hcomp).trans
          (Category.assoc _ _ _).symm)))


/-- The original D(J[0]) coefficient is the actual chosen Cartesian unit.
The first leg uses the INVERSE of the public Delta[0] to J[0] inclusion Iso. -/
def coefficientZeroUnitIso : coefficient.{u}.obj ⦋0⦌ ≅ (𝟙_ SimplicialSpace.{u}) :=
  discreteInnerFunctor.mapIso SSet.FreeGroupoidSimplex.zeroIso.symm ≪≫
    discreteInnerFunctor.mapIso
      (SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso
        CartesianMonoidalCategory.isTerminalTensorUnit) ≪≫
    SimplicialSpace.WalkingEUnit.coherentUnitIso

private theorem curryUnitSecondProjection (W : SimplicialSpace.{u}) :
    MonoidalClosed.curry
      (CartesianMonoidalCategory.snd (𝟙_ SimplicialSpace.{u}) W) =
        (MonoidalClosed.unitNatIso (C := SimplicialSpace.{u})).hom.app W := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_eq]
  have h := CategoryTheory.conjugateEquiv_counit
    (CategoryTheory.Adjunction.id (C := SimplicialSpace.{u}))
    (CategoryTheory.ihom.adjunction (𝟙_ SimplicialSpace.{u}))
    (MonoidalCategory.leftUnitorNatIso SimplicialSpace.{u}).hom W
  change (𝟙_ SimplicialSpace.{u}) ◁
      (MonoidalClosed.unitNatIso (C := SimplicialSpace.{u})).hom.app W ≫
        (CategoryTheory.ihom.ev (𝟙_ SimplicialSpace.{u})).app W =
      (λ_ W).hom ≫ 𝟙 W at h
  rw [Category.comp_id, CartesianMonoidalCategory.leftUnitor_hom] at h
  exact h.symm

/-- The same original zero power, transported through the actual coefficient Iso. -/
def powerZeroUnitIso (W : SimplicialSpace.{u}) :
    (powerDiagram W).obj (op ⦋0⦌) ≅ W :=
  ((MonoidalClosed.internalHom (C := SimplicialSpace.{u})).mapIso
    coefficientZeroUnitIso.symm.op).app W ≪≫
      MonoidalClosed.unitIsoSelf (X := W)

/-- The literal original curry-snd coaugmentation is the inverse of that zero-power Iso. -/
theorem constantPowerSection_zero_comparison (W : SimplicialSpace.{u}) :
    (constantPowerSection W).app (op ⦋0⦌) ≫ (powerZeroUnitIso W).hom = 𝟙 W := by
  change MonoidalClosed.curry
      (CartesianMonoidalCategory.snd (coefficient.obj ⦋0⦌) W) ≫
        ((MonoidalClosed.pre coefficientZeroUnitIso.inv).app W ≫
          (MonoidalClosed.unitIsoSelf (X := W)).hom) = 𝟙 W
  rw [← Category.assoc, MonoidalClosed.curry_pre_app,
    CartesianMonoidalCategory.whiskerRight_snd, curryUnitSecondProjection]
  change (MonoidalClosed.unitNatIso (C := SimplicialSpace.{u})).hom.app W ≫
      (MonoidalClosed.unitNatIso (C := SimplicialSpace.{u})).inv.app W = 𝟙 W
  exact (MonoidalClosed.unitNatIso (C := SimplicialSpace.{u})).hom_inv_id_app W

/-- An equation with the actual inverse map, rather than a supplied isomorphic unit. -/
theorem constantPowerSection_zero_eq_inverse (W : SimplicialSpace.{u}) :
    (constantPowerSection W).app (op ⦋0⦌) = (powerZeroUnitIso W).inv := by
  apply (cancel_mono (powerZeroUnitIso W).hom).1
  rw [constantPowerSection_zero_comparison, Iso.inv_hom_id]
  rfl

/-- At inner degree zero every original outer row sees exactly the same constant section.
This is an owned constructor equation: rowSection stays private in this SAME module. -/
theorem rawCompletionUnit_innerZero (W : SimplicialSpace.{u})
    (k : SimplexCategoryᵒᵖ) :
    ((rawCompletionUnit W).hom.app k).app (op ⦋0⦌) =
      (((constantPowerSection W).app (op ⦋0⦌)).hom.app k).app (op ⦋0⦌) := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- The actual raw coaugmentation is bijective on the original inner-zero vertices
in EVERY original outer row, without RF, Segal or completeness hypotheses. -/
theorem rawCompletionUnit_innerZero_bijective (W : SimplicialSpace.{u})
    (k : SimplexCategoryᵒᵖ) :
    Function.Bijective (((rawCompletionUnit W).hom.app k).app (op ⦋0⦌)) := by
  rw [rawCompletionUnit_innerZero, constantPowerSection_zero_eq_inverse]
  let e : (W.diagram.obj k).obj (op ⦋0⦌) ≅
      (((powerDiagram W).obj (op ⦋0⦌)).diagram.obj k).obj (op ⦋0⦌) :=
    ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌)).mapIso
      ((forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet).obj k).mapIso
        (powerZeroUnitIso W).symm)
  exact e.toEquiv.bijective

end SimplicialSpace.RezkCompletionRaw
