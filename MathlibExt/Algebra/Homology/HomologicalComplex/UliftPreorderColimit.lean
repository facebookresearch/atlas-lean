/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.ModuleCat.UliftPreorderColimit
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Additive

/-!
# Universe lifts preserve preorder colimits of complexes

Module direct-limit colimits transport through `ULift` at each degree.
Complex evaluation assembles these degreewise colimits and proves
preservation for the specified ring and index universes.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe r i m z j

namespace ModuleCat

variable (R : Type r) [Ring R] {I : Type i} [Preorder I]
  {α : Type j} (c : ComplexShape α)
  (K : I ⥤ HomologicalComplex (ModuleCat.{max i m} R) c)

/-- The complex universe-lift functor preserves every preorder-diagram colimit. -/
instance uliftComplexFunctor_preservesPreorderColimit :
    PreservesColimit K ((uliftFunctor.{z, max i m} R).mapHomologicalComplex c) := by
  let U := uliftFunctor.{z, max i m} R
  have (n : α) : HasColimit (K ⋙ HomologicalComplex.eval (ModuleCat.{max i m} R) c n) :=
    ⟨⟨⟨directLimitCoconeOfFunctor (K ⋙ HomologicalComplex.eval (ModuleCat.{max i m} R) c n),
      directLimitCoconeOfFunctorIsColimit
        (K ⋙ HomologicalComplex.eval (ModuleCat.{max i m} R) c n)⟩⟩⟩
  let s := HomologicalComplex.coconeOfHasColimitEval K
  have hs : IsColimit s := HomologicalComplex.isColimitCoconeOfHasColimitEval K
  refine preservesColimit_of_preserves_colimit_cocone hs
    (HomologicalComplex.isColimitOfEval _ _ (fun n => ?_))
  change IsColimit (U.mapCocone
    ((HomologicalComplex.eval (ModuleCat.{max i m} R) c n).mapCocone s))
  exact isColimitOfPreserves U
    (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat.{max i m} R) c n) hs)

end ModuleCat
