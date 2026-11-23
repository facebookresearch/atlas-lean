/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.Loop.OriginalDoublePathInterchange
import MathlibExt.CategoryTheory.Monoidal.Closed.InternalHomInterchange

/-!
# Both original endpoint directions of the original path-square swap

The whole original internal swap exchanges evaluation in both coordinates
at every actual unit point. The point insertion is an equality of the
actual simplicial tensor maps. Specialization retains the original
Delta[0] unit comparison and both original vertex inclusions, followed by
the SAME eval-zero and eval-one functions. Both comparison directions,
both endpoints and all original target-map naturalities are included.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped Simplicial MonoidalClosed SSet.modelCategoryQuillen


namespace SSet.OriginalLoopPathEndpointGeometry

open CategoryTheory.MonoidalClosed.OriginalLoopInterchangeGeometry
open SSet.OriginalLoopPathInterchangeGeometry
open CategoryTheory.MonoidalClosed.OriginalPointEvaluationClauseGeometry

/-- Evaluation at the entire original unit-point map is an actual natural transformation. -/
def originalPointEvaluationNatTrans (I : SSet.{u}) (t : (𝟙_ SSet.{u}) ⟶ I) :
    ihom I ⟶ 𝟭 SSet.{u} :=
  pre t ≫ unitNatIso.inv

/-- Every full evaluation component retains both original closed maps. -/
theorem originalPointEvaluationNatTrans_app (I : SSet.{u})
    (t : (𝟙_ SSet.{u}) ⟶ I) (X : SSet.{u}) :
    (originalPointEvaluationNatTrans I t).app X =
      (pre t).app X ≫ (unitIsoSelf (X := X)).hom := rfl

/-- The full unit-point evaluation retains every original target-map naturality. -/
theorem originalPointEvaluationNatTrans_naturality (I : SSet.{u})
    (t : (𝟙_ SSet.{u}) ⟶ I) {X Y : SSet.{u}} (f : X ⟶ Y) :
    (ihom I).map f ≫ (originalPointEvaluationNatTrans I t).app Y =
      (originalPointEvaluationNatTrans I t).app X ≫ f :=
  (originalPointEvaluationNatTrans I t).naturality f

/-- Composing the full original evaluation is restriction of the SAME entire uncurried map. -/
theorem originalPointEvaluationNatTrans_comp (I : SSet.{u})
    (t : (𝟙_ SSet.{u}) ⟶ I) {A X : SSet.{u}} (f : A ⟶ (ihom I).obj X) :
    f ≫ (originalPointEvaluationNatTrans I t).app X =
      (λ_ A).inv ≫ t ▷ A ≫ uncurry f := by
  rw [originalPointEvaluationNatTrans_app, ← Category.assoc]
  have h : f ≫ (pre t).app X = curry (t ▷ A ≫ uncurry f) :=
    (congrArg (fun e => e ≫ (pre t).app X) (curry_uncurry f).symm).trans
      (curry_pre_app t (uncurry f))
  exact (congrArg (fun e => e ≫ (unitIsoSelf (X := X)).hom) h).trans
    (SSet.curry_unitIsoSelf (t ▷ A ≫ uncurry f))

/-- The actual original unit-point insertion exchanges the two entire tensor coordinates. -/
@[reassoc]
theorem originalPointInsertion_interchange (I A : SSet.{u})
    (t : (𝟙_ SSet.{u}) ⟶ I) :
    I ◁ ((λ_ A).inv ≫ t ▷ A) ≫ (α_ I I A).inv ≫
        (β_ I I).inv ▷ A ≫ (α_ I I A).hom =
      (λ_ (I ⊗ A)).inv ≫ t ▷ (I ⊗ A) := by
  apply NatTrans.ext
  funext n
  exact ConcreteCategory.hom_ext _ _ (fun z => rfl)

/-- The whole original forward closed swap exchanges evaluation with the original inner map. -/
theorem originalSelfInterchange_hom_outer_evaluation (I X : SSet.{u})
    (t : (𝟙_ SSet.{u}) ⟶ I) :
    (originalSelfInterchangeNatIso I).hom.app X ≫
        (originalPointEvaluationNatTrans I t).app ((ihom I).obj X) =
      (ihom I).map ((originalPointEvaluationNatTrans I t).app X) := by
  apply uncurry_injective
  rw [originalPointEvaluationNatTrans_comp, uncurry_natural_left, uncurry_natural_left,
    originalSelfInterchangeNatIso_hom_double_uncurry, uncurry_ihom_map,
    originalPointEvaluationNatTrans_comp]
  simp only [uncurry_eq]
  rw [← whiskerLeft_comp_assoc]
  exact originalPointInsertion_interchange_assoc I
    ((ihom I).obj ((ihom I).obj X)) t
      (I ◁ (ihom.ev I).app ((ihom I).obj X) ≫ (ihom.ev I).app X)

/-- The whole original forward closed swap exchanges the entire inner map with evaluation. -/
theorem originalSelfInterchange_hom_inner_evaluation (I X : SSet.{u})
    (t : (𝟙_ SSet.{u}) ⟶ I) :
    (originalSelfInterchangeNatIso I).hom.app X ≫
        (ihom I).map ((originalPointEvaluationNatTrans I t).app X) =
      (originalPointEvaluationNatTrans I t).app ((ihom I).obj X) := by
  rw [← originalSelfInterchange_hom_outer_evaluation I X t, ← Category.assoc]
  have h := congrArg (fun e => e.app X) (originalSelfInterchangeNatIso_involution I)
  exact (congrArg (fun e => e ≫ (originalPointEvaluationNatTrans I t).app
    ((ihom I).obj X)) h).trans (Category.id_comp _)

/-- The entire inverse original closed map exchanges the same outer evaluation. -/
theorem originalSelfInterchange_inv_outer_evaluation (I X : SSet.{u})
    (t : (𝟙_ SSet.{u}) ⟶ I) :
    (originalSelfInterchangeNatIso I).inv.app X ≫
        (originalPointEvaluationNatTrans I t).app ((ihom I).obj X) =
      (ihom I).map ((originalPointEvaluationNatTrans I t).app X) := by
  rw [← originalSelfInterchangeNatIso_hom_eq_inv]
  exact originalSelfInterchange_hom_outer_evaluation I X t

/-- The entire inverse original closed map exchanges the same inner evaluation. -/
theorem originalSelfInterchange_inv_inner_evaluation (I X : SSet.{u})
    (t : (𝟙_ SSet.{u}) ⟶ I) :
    (originalSelfInterchangeNatIso I).inv.app X ≫
        (ihom I).map ((originalPointEvaluationNatTrans I t).app X) =
      (originalPointEvaluationNatTrans I t).app ((ihom I).obj X) := by
  rw [← originalSelfInterchangeNatIso_hom_eq_inv]
  exact originalSelfInterchange_hom_inner_evaluation I X t

/-- The full outer original evaluation is retained as an entire natural transformation. -/
def originalOuterPointEvaluationNatTrans (I : SSet.{u}) (t : (𝟙_ SSet.{u}) ⟶ I) :
    ihom I ⋙ ihom I ⟶ ihom I :=
  Functor.whiskerLeft (ihom I) (originalPointEvaluationNatTrans I t)

/-- The full inner original evaluation is retained as an entire natural transformation. -/
def originalInnerPointEvaluationNatTrans (I : SSet.{u}) (t : (𝟙_ SSet.{u}) ⟶ I) :
    ihom I ⋙ ihom I ⟶ ihom I :=
  Functor.whiskerRight (originalPointEvaluationNatTrans I t) (ihom I)

/-- Both complete original outer/inner transformations agree after the whole forward swap. -/
theorem originalSelfInterchange_hom_outer_evaluation_whole (I : SSet.{u})
    (t : (𝟙_ SSet.{u}) ⟶ I) :
    (originalSelfInterchangeNatIso I).hom ≫ originalOuterPointEvaluationNatTrans I t =
      originalInnerPointEvaluationNatTrans I t := by
  apply NatTrans.ext
  funext X
  exact originalSelfInterchange_hom_outer_evaluation I X t

/-- Both complete original inner/outer transformations agree after the whole forward swap. -/
theorem originalSelfInterchange_hom_inner_evaluation_whole (I : SSet.{u})
    (t : (𝟙_ SSet.{u}) ⟶ I) :
    (originalSelfInterchangeNatIso I).hom ≫ originalInnerPointEvaluationNatTrans I t =
      originalOuterPointEvaluationNatTrans I t := by
  apply NatTrans.ext
  funext X
  exact originalSelfInterchange_hom_inner_evaluation I X t

/-- The SAME original Delta-zero comparison and original vertex inclusion define every endpoint. -/
def originalEndpointUnitPoint (i : Fin 2) : (𝟙_ SSet.{u}) ⟶ (Δ[1] : SSet.{u}) :=
  SSet.Δ0IsoUnit.inv ≫ SSet.stdSimplex.δ i

/-- The whole original initial-endpoint function is evaluation at its exact original unit point. -/
theorem originalEvalZero_eq (X : SSet.{u}) :
    (SSet.eval₀ : pathSpace X ⟶ X) =
      (originalPointEvaluationNatTrans (Δ[1] : SSet.{u})
        (originalEndpointUnitPoint (1 : Fin 2))).app X := by
  rw [SSet.eval₀_eq_pre_app, SSet.ihomZeroIso_hom,
    originalPointEvaluationNatTrans_app]
  exact originalPreCompositionEvaluation_app SSet.Δ0IsoUnit.inv
    (SSet.stdSimplex.δ (1 : Fin 2)) X

/-- The whole original final-endpoint function is evaluation at its exact original unit point. -/
theorem originalEvalOne_eq (X : SSet.{u}) :
    (SSet.eval₁ : pathSpace X ⟶ X) =
      (originalPointEvaluationNatTrans (Δ[1] : SSet.{u})
        (originalEndpointUnitPoint (0 : Fin 2))).app X := by
  unfold SSet.eval₁
  rw [originalPointEvaluationNatTrans_app]
  exact originalPreCompositionEvaluation_app SSet.Δ0IsoUnit.inv
    (SSet.stdSimplex.δ (0 : Fin 2)) X

/-- The entire original forward swap sends the original outer initial endpoint to the inner one. -/
theorem originalDoublePathSwap_hom_evalZero (X : SSet.{u}) :
    (originalDoublePathSwapIso X).hom ≫
        (SSet.eval₀ : pathSpace (pathSpace X) ⟶ pathSpace X) =
      (ihom (Δ[1] : SSet.{u})).map (SSet.eval₀ : pathSpace X ⟶ X) := by
  rw [originalEvalZero_eq, originalEvalZero_eq]
  exact originalSelfInterchange_hom_outer_evaluation (Δ[1] : SSet.{u}) X _

/-- The entire original forward swap sends the original outer final endpoint to the inner one. -/
theorem originalDoublePathSwap_hom_evalOne (X : SSet.{u}) :
    (originalDoublePathSwapIso X).hom ≫
        (SSet.eval₁ : pathSpace (pathSpace X) ⟶ pathSpace X) =
      (ihom (Δ[1] : SSet.{u})).map (SSet.eval₁ : pathSpace X ⟶ X) := by
  rw [originalEvalOne_eq, originalEvalOne_eq]
  exact originalSelfInterchange_hom_outer_evaluation (Δ[1] : SSet.{u}) X _

/-- The full original forward swap sends the original inner initial endpoint to the outer one. -/
theorem originalDoublePathSwap_hom_map_evalZero (X : SSet.{u}) :
    (originalDoublePathSwapIso X).hom ≫
        (ihom (Δ[1] : SSet.{u})).map (SSet.eval₀ : pathSpace X ⟶ X) =
      (SSet.eval₀ : pathSpace (pathSpace X) ⟶ pathSpace X) := by
  rw [originalEvalZero_eq, originalEvalZero_eq]
  exact originalSelfInterchange_hom_inner_evaluation (Δ[1] : SSet.{u}) X _

/-- The full original forward swap sends the original inner final endpoint to the outer one. -/
theorem originalDoublePathSwap_hom_map_evalOne (X : SSet.{u}) :
    (originalDoublePathSwapIso X).hom ≫
        (ihom (Δ[1] : SSet.{u})).map (SSet.eval₁ : pathSpace X ⟶ X) =
      (SSet.eval₁ : pathSpace (pathSpace X) ⟶ pathSpace X) := by
  rw [originalEvalOne_eq, originalEvalOne_eq]
  exact originalSelfInterchange_hom_inner_evaluation (Δ[1] : SSet.{u}) X _

/-- The same complete inverse original swap retains the original initial endpoint equation. -/
theorem originalDoublePathSwap_inv_evalZero (X : SSet.{u}) :
    (originalDoublePathSwapIso X).inv ≫
        (SSet.eval₀ : pathSpace (pathSpace X) ⟶ pathSpace X) =
      (ihom (Δ[1] : SSet.{u})).map (SSet.eval₀ : pathSpace X ⟶ X) := by
  rw [originalEvalZero_eq, originalEvalZero_eq]
  exact originalSelfInterchange_inv_outer_evaluation (Δ[1] : SSet.{u}) X _

/-- The same complete inverse original swap retains the original final endpoint equation. -/
theorem originalDoublePathSwap_inv_evalOne (X : SSet.{u}) :
    (originalDoublePathSwapIso X).inv ≫
        (SSet.eval₁ : pathSpace (pathSpace X) ⟶ pathSpace X) =
      (ihom (Δ[1] : SSet.{u})).map (SSet.eval₁ : pathSpace X ⟶ X) := by
  rw [originalEvalOne_eq, originalEvalOne_eq]
  exact originalSelfInterchange_inv_outer_evaluation (Δ[1] : SSet.{u}) X _

/-- The same full inverse original swap retains the entire inner initial endpoint equation. -/
theorem originalDoublePathSwap_inv_map_evalZero (X : SSet.{u}) :
    (originalDoublePathSwapIso X).inv ≫
        (ihom (Δ[1] : SSet.{u})).map (SSet.eval₀ : pathSpace X ⟶ X) =
      (SSet.eval₀ : pathSpace (pathSpace X) ⟶ pathSpace X) := by
  rw [originalEvalZero_eq, originalEvalZero_eq]
  exact originalSelfInterchange_inv_inner_evaluation (Δ[1] : SSet.{u}) X _

/-- The same full inverse original swap retains the entire inner final endpoint equation. -/
theorem originalDoublePathSwap_inv_map_evalOne (X : SSet.{u}) :
    (originalDoublePathSwapIso X).inv ≫
        (ihom (Δ[1] : SSet.{u})).map (SSet.eval₁ : pathSpace X ⟶ X) =
      (SSet.eval₁ : pathSpace (pathSpace X) ⟶ pathSpace X) := by
  rw [originalEvalOne_eq, originalEvalOne_eq]
  exact originalSelfInterchange_inv_inner_evaluation (Δ[1] : SSet.{u}) X _

end SSet.OriginalLoopPathEndpointGeometry
