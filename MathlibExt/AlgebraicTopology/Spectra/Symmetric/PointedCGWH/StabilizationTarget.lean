/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OperatorStabilizationK

/-!
# Target naturality of symmetric sphere actions

Relates the operator-generator sphere action to the reconstructed module pairing.
Postcomposition in the target finite-set index is compatible with both the action and its
closed-adjunction transpose.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory BraidedCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.CurrentFree

private abbrev I := Operad.SmallFinBijGroupoid
open PointedCGWH.SymmetricModulePresentation

theorem action_operatorGenerator_eq_reconstructed
    (E : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v})
    (a n k : Operad.SmallFinBijGroupoid) (f : a ⊗ n ⟶ k) :
    action (PointedCGWH.symmetricOperatorObj n) (PointedCGWH.symmetricOperatorObj k)
      (PointedCGWH.sphereSequence.functor.obj a) (operatorGenerator a n k f) E =
      reconstructedArrowAction E a n k f := by
  let M := PointedCGWH.sphereSequence.{u, v}.functor.obj a
  let X := E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n)
  let H := PointedCGWH.symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}]
    PointedCGWH.symmetricOperatorObj.{u, v} k
  let p : M ⟶ H := operatorGenerator a n k f
  let q := E.toEnrichedFunctor.map (PointedCGWH.symmetricOperatorObj n)
      (PointedCGWH.symmetricOperatorObj k)
  change (p ▷ X) ≫ (β_ X H).inv ≫ MonoidalClosed.uncurry q =
    (β_ M X).hom ≫ MonoidalClosed.uncurry (p ≫ q)
  rw [MonoidalClosed.uncurry_natural_left]
  have hb := braiding_inv_naturality_left p X
  have hs := SymmetricCategory.braiding_swap_eq_inv_braiding X M
  have h := congrArg (fun t => t ≫ MonoidalClosed.uncurry q)
    (hb.trans (congrArg (fun t => t ≫ (X ◁ p)) hs.symm))
  simpa only [Category.assoc] using h

theorem action_operatorGenerator_target
    (E : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v})
    (a n k l : Operad.SmallFinBijGroupoid) (f : a ⊗ n ⟶ k) (g : k ⟶ l) :
    action (PointedCGWH.symmetricOperatorObj n) (PointedCGWH.symmetricOperatorObj k)
        (PointedCGWH.sphereSequence.functor.obj a) (operatorGenerator a n k f) E ≫
      ((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj E).functor.map g =
    action (PointedCGWH.symmetricOperatorObj n) (PointedCGWH.symmetricOperatorObj l)
      (PointedCGWH.sphereSequence.functor.obj a) (operatorGenerator a n l (f ≫ g)) E := by
  exact (congrArg
    (fun t => t ≫ ((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj E).functor.map g)
    (action_operatorGenerator_eq_reconstructed E a n k f)).trans
      ((reconstructedArrowAction_target E a n k l f g).trans
        (action_operatorGenerator_eq_reconstructed E a n l (f ≫ g)).symm)

theorem adjoint_operatorGenerator_target
    (E : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v})
    (a n k l : Operad.SmallFinBijGroupoid) (f : a ⊗ n ⟶ k) (g : k ⟶ l) :
    adjoint (PointedCGWH.symmetricOperatorObj n) (PointedCGWH.symmetricOperatorObj k)
        (PointedCGWH.sphereSequence.functor.obj a) (operatorGenerator a n k f) E ≫
      (ihom (PointedCGWH.sphereSequence.functor.obj a)).map
        (((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj E).functor.map g) =
    adjoint (PointedCGWH.symmetricOperatorObj n) (PointedCGWH.symmetricOperatorObj l)
      (PointedCGWH.sphereSequence.functor.obj a) (operatorGenerator a n l (f ≫ g)) E := by
  exact (MonoidalClosed.curry_natural_right _ _).symm.trans
    (congrArg MonoidalClosed.curry (action_operatorGenerator_target E a n k l f g))

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.CurrentFree
