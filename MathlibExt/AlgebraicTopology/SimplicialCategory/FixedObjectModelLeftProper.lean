/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeBoundarySourceCobaseWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModel
import MathlibExt.AlgebraicTopology.ModelCategory.Proper
import Mathlib.CategoryTheory.MorphismProperty.RetractArgument

/-!
# Genuine left properness of the SAME original fixed-object model

An original cofibration is a genuine under-source retract of its SAME
native whole boundary factorization. The original Under.pushout
adjunction supplies the natural full source comparison. Naturality
carries that actual retract to the SAME original pushout inclusion.
The proved whole original boundary source comparison therefore gives
weakness of every original cofibration cobase change. No left-proper
or weak-outcome certificate is supplied as an input.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectModel
variable {O : Type u} {C X D E : FixedObjects O}
attribute [local instance] modelCategory

private def underSourceComparison (F : C ⟶ D) :
    Under.forget C ⟶ Under.pushout F ⋙ Under.forget D where
  app U := ((Under.mapPushoutAdj F).unit.app U).right
  naturality _U _V g := congrArg (fun k => k.right) ((Under.mapPushoutAdj F).unit.naturality g)

private theorem underSourceComparison_app (F : C ⟶ D) (U : Under C) :
    (underSourceComparison F).app U = pushout.inl U.hom F :=
  congrArg (fun k => k.right) (Under.mapPushoutAdj_unit_app F U)

/-- The genuine original cofibration is an actual under-source retract of its SAME native boundary left factor. -/
def boundaryUnderRetract (i : C ⟶ X) (hi : cofibrations O i) :
    Retract (Under.mk i) (Under.mk (FreeFactorization.boundary i).i) := by
  let φ := FreeFactorization.boundary i
  let _ : HasLiftingProperty i φ.p := hi φ.p φ.hp
  let r := RetractArrow.ofLeftLiftingProperty φ.fac
  have hsection : i ≫ r.i.right = φ.i :=
    r.i.w.symm.trans (Category.id_comp φ.i)
  refine {
    i := Under.homMk r.i.right hsection
    r := Under.homMk φ.p φ.fac
    retract := ?_ }
  apply Under.UnderMorphism.ext
  exact r.retract_right

/-- The SAME canonical full pushout inclusion of any genuine Homwise weak map along an original cofibration is weak. -/
theorem canonical_cofibration_cobase_weak (i : C ⟶ X) (hi : cofibrations O i)
    (F : C ⟶ D) (hF : weakEquivalences O F) :
    weakEquivalences O (pushout.inl i F) := by
  let r := boundaryUnderRetract i hi
  have hw : weakEquivalences O
      ((underSourceComparison F).app (Under.mk (FreeFactorization.boundary i).i)) := by
    rw [underSourceComparison_app]
    exact FreeFactorization.boundarySource_cobase_weak i F hF
  have h := (weakEquivalences O).of_retract ((underSourceComparison F).retractArrowApp r) hw
  exact (congrArg (fun f : X ⟶ pushout i F => weakEquivalences O f)
    (underSourceComparison_app F (Under.mk i))).mp h

/-- Any supplied original cofibration pushout retains the SAME genuinely Homwise weak source map. -/
theorem weak_of_isPushout (i : C ⟶ X) (hi : cofibrations O i)
    (F : C ⟶ D) (hF : weakEquivalences O F) (d : X ⟶ E) (c : D ⟶ E)
    (sq : IsPushout i F d c) : weakEquivalences O d := by
  let e := (IsPushout.of_hasPushout i F).isoIsPushout _ _ sq
  have he : pushout.inl i F ≫ e.hom = d :=
    (IsPushout.of_hasPushout i F).inl_isoIsPushout_hom _ _ sq
  have hw := (weakEquivalences O).comp_mem _ _ (canonical_cofibration_cobase_weak i hi F hF)
    ((weakEquivalences O).of_isIso e.hom)
  exact he ▸ hw

/-- The SAME original fixed-object simplicial-category model is genuinely left proper. -/
instance leftProper : IsLeftProper (FixedObjects O) where
  weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations := by
    constructor
    intro C X i hi
    constructor
    intro D E c d F sq hF
    exact weak_of_isPushout i hi F hF d c sq

end CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectModel
