/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all MathlibExt.CategoryTheory.Operad.Tensor.AlgebraRestriction
import Batteries.Tactic.Lint

/-!
# Public tensor algebra restriction

Arbitrary operad maps keep each original carrier and its operation, unit,
substitution and algebra-morphism equations through the focused restriction API.
-/

set_option autoImplicit false
noncomputable section
universe uc u v

open CategoryTheory Operad Operad.Tensor

namespace AlgebraRestrictionPublicTests

variable {Color : Type uc} {C : Type u} [Category.{v} C] [FiniteTensor C]
  {O P : ColoredOperadObj Color C} (f : O ⟶ P)

example : Category (Algebra O) := inferInstance
example (A : Algebra P) : (Algebra.restrict f A).carrier = A.carrier := rfl

example (A : Algebra P) (d : Color) (q : AnalyticIndex Color d) :
    (Algebra.restrict f A).operations.app d q =
      (analyticSummandCollectionMap A.carrier f.toCollectionHom).app q ≫ A.operations.app d q := rfl

example (A : Algebra P) (d : Color) :
    unitInsertion O A.carrier d ≫ (Algebra.restrict f A).operations.app d (AnalyticIndex.unary d) =
      𝟙 (A.carrier d) :=
  (Algebra.restrict f A).unit d

example (A : Algebra P) (s : ColoredSubstitutionData Color) :
    algebraSubstitutionInner (Algebra.restrict f A).operations s =
      operadSubstitutionInputs O A.carrier s ≫
        (Algebra.restrict f A).operations.app s.outputColor (profileInputs s.totalProfile) :=
  (Algebra.restrict f A).substitution s

example {A B : Algebra P} (g : A ⟶ B) (d : Color) :
    ((restrictionFunctor f).map g).hom d = g.hom d := rfl

example : restrictionFunctor f ⋙ Algebra.forget O = Algebra.forget P := by
  exact CategoryTheory.Functor.ext (fun _ => rfl) (fun A B g => by
    funext d
    with_unfolding_all
      exact (Category.id_comp (g.hom d)).symm.trans
        (congrArg (𝟙 _ ≫ ·) (Category.comp_id (g.hom d)).symm))

end AlgebraRestrictionPublicTests

#print axioms CategoryTheory.Operad.Tensor.Algebra.restrict
#print axioms CategoryTheory.Operad.Tensor.restrictionFunctor
#print axioms CategoryTheory.Operad.Tensor.Restriction.unitInsertion_comp
#print axioms CategoryTheory.Operad.Tensor.Restriction.substitutionInner
#print axioms CategoryTheory.Operad.Tensor.Restriction.substitutionInputs
#lint only unusedArguments in MathlibExt.CategoryTheory.Operad.Tensor.AlgebraRestriction
#lint+ in MathlibExt.CategoryTheory.Operad.Tensor.AlgebraRestriction
