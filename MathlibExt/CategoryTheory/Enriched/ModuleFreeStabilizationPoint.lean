/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.FreeAdjunctTransport
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FreeStabilizationMapping

/-!
# Adjuncts of module free-stabilization maps

For a module-to-enriched-diagram equivalence and compatible free/evaluation adjunctions,
the adjunct of a transported stabilization map is its defining enriched Hom label. The
formula retains the evaluation comparisons, free-source isomorphisms and carrier
comparison.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uC vC uV vV uJ
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

namespace NativeOmegaRecovery.ModuleFreeStabilizationPoint
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  (A : CommMon C)
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] {J : Type uJ} [EnrichedCategory V J]
  (E : Mod C A.X ≌ EnrichedFunctorCat V J)

/-- The whole actual source adjunct equation retains the original evaluation
comparison, free source maps and carrier counit. -/
def Equation (a b : J) (L : V ⥤ Mod C A.X) (R : Mod C A.X ⥤ V)
    (adj : L ⊣ R) (r : E.functor ⋙ evaluation a ≅ R)
    (L' : V ⥤ Mod C A.X) (R' : Mod C A.X ⥤ V)
    (adj' : L' ⊣ R') (r' : E.functor ⋙ evaluation b ≅ R')
    (K : V) (D : K ⟶ (a ⟶[V] b)) : Prop :=
    adj'.homEquiv K (L.obj (𝟙_ V))
        (ModuleFreeSourceTransport.sourceArrow A E
          ((FreeAdjunctionSource.comparison E a L R adj r).app (𝟙_ V))
          ((FreeAdjunctionSource.comparison E b L' R' adj' r').app K)
          (CurrentFree.stabilization a b K D)) ≫
      r'.inv.app (L.obj (𝟙_ V)) =
        D ≫ (λ_ (a ⟶[V] b)).inv ≫
          component ((FreeAdjunctionSource.operatorIso E a L R adj r).inv.app (𝟙_ V)) b

/-- Every actual stabilization obeys that whole original source adjunct equation. -/
theorem equation (a b : J) (L : V ⥤ Mod C A.X) (R : Mod C A.X ⥤ V)
    (adj : L ⊣ R) (r : E.functor ⋙ evaluation a ≅ R)
    (L' : V ⥤ Mod C A.X) (R' : Mod C A.X ⥤ V)
    (adj' : L' ⊣ R') (r' : E.functor ⋙ evaluation b ≅ R')
    (K : V) (D : K ⟶ (a ⟶[V] b)) : Equation A E a b L R adj r L' R' adj' r' K D := by
  let f := CurrentFree.stabilization a b K D
  let X := E.functor.obj (L.obj (𝟙_ V))
  let g := (FreeAdjunctionSource.operatorIso E a L R adj r).inv.app (𝟙_ V)
  have hp := ModuleFreeAdjunctTransport.source_point A E a b L R adj r
    L' R' adj' r' (𝟙_ V) K f
  have hPost := Free.evaluate_postcomp b K f g
  have hEval := CurrentFree.stabilization_adjunct a b K D
  rw [Free.adjunction_homEquiv] at hEval
  let F := Free.object a (𝟙_ V)
  change Free.evaluate b K F f = D ≫ (λ_ (a ⟶[V] b)).inv at hEval
  let t : F.toEnrichedFunctor.obj b ⟶ X.toEnrichedFunctor.obj b := component g b
  have hEvalPost := congrArg (fun z : K ⟶ F.toEnrichedFunctor.obj b => z ≫ t) hEval
  have hEvalPost' : Free.evaluate b K F f ≫ (EnrichedFunctorCat.evaluation b).map g =
      D ≫ (λ_ (a ⟶[V] b)).inv ≫ component g b :=
    hEvalPost.trans (Category.assoc D (λ_ (a ⟶[V] b)).inv (component g b))
  exact hp.trans (hPost.trans hEvalPost')

end NativeOmegaRecovery.ModuleFreeStabilizationPoint
