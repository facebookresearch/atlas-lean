/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ProductAssociativity
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterAdjunction

/-!
# The original marked parameter action retains multiplication

Two original maximally marked parameter products are the same whole
product parameter, through the native associator and maximal-marking
identity. This is an isomorphism in the supplied original marked slice.
Parameter maps in either factor retain the same full maps and base
projection. These are action laws without a marked-model assumption.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory

namespace SSet.Marked

/-- Two original maximal parameter products retain the same whole product parameter and actual base projection. -/
def overParameterMultiplicationIso (Z : Marked.{u}) (X : Over Z) (A K : SSet.{u}) :
    overParameter Z (overParameter Z X K) A ≅ overParameter Z X (A ⊗ K) := by
  let e := (prodAssociator (max A) (max K) X.left).symm ≪≫ prodIso (maxProductIso A K) (Iso.refl X.left)
  exact Over.isoMk e (by apply Hom.ext; ext n z; rfl)

/-- First parameter maps retain their original whole maps under the native parameter multiplication comparison. -/
theorem overParameterMultiplicationIso_natural_left (Z : Marked.{u}) (X : Over Z)
    {A A' : SSet.{u}} (a : A ⟶ A') (K : SSet.{u}) :
    (overParameterFunctor Z (overParameter Z X K)).map a ≫
        (overParameterMultiplicationIso Z X A' K).hom =
      (overParameterMultiplicationIso Z X A K).hom ≫
        (overParameterFunctor Z X).map (a ⊗ₘ 𝟙 K) := by
  apply Over.OverMorphism.ext
  apply Hom.ext
  rfl

/-- The inverse parameter comparison also retains the original first-factor map literally. -/
theorem overParameterMultiplicationIso_inv_natural_left (Z : Marked.{u}) (X : Over Z)
    {A A' : SSet.{u}} (a : A ⟶ A') (K : SSet.{u}) :
    (overParameterMultiplicationIso Z X A K).inv ≫
        (overParameterFunctor Z (overParameter Z X K)).map a =
      (overParameterFunctor Z X).map (a ⊗ₘ 𝟙 K) ≫
        (overParameterMultiplicationIso Z X A' K).inv := by
  apply Over.OverMorphism.ext
  apply Hom.ext
  rfl

/-- Multiplication of the original marked parameter action is a genuine natural isomorphism. -/
def overParameterMultiplicationNatIso (Z : Marked.{u}) (X : Over Z) (K : SSet.{u}) :
    overParameterFunctor Z (overParameter Z X K) ≅ tensorRight K ⋙ overParameterFunctor Z X :=
  NatIso.ofComponents (fun A => overParameterMultiplicationIso Z X A K)
    (fun a => overParameterMultiplicationIso_natural_left Z X a K)

end SSet.Marked
