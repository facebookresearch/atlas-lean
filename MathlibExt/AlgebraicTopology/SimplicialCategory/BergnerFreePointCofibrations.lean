/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerFreeObjects
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerFixedObjectGlobalLifting
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModelClasses

/-!
# Genuine original free-point injections are global C0 cofibrations

Choose the exact supplied top object at its original label and actual
object preimages at every other label. The full original free-object
universal property gives the whole lift and both entire triangles.
Every point injection therefore lifts against all original C0 right
maps, with no global model or interval acyclicity assumption.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.BergnerFreeObjects

/-- Every original point injection lifts against every full enriched map surjective on its SAME original objects. -/
theorem injection_hasLiftingProperty (O : Type u) (x : O) {C D : Carrier.{u}} (r : C ⟶ D)
    (hr : Function.Surjective r.obj) : HasLiftingProperty (injection O x) r := by
  classical
  refine ⟨fun {top bottom} sq => ?_⟩
  let b : O → D := fun t => bottom.obj (vertex O t)
  have hx : r.obj (top.obj PUnit.unit) = b x :=
    congrArg (fun F : BergnerObjects.point.{u} ⟶ D => F.obj PUnit.unit) sq.w
  let a : O → C := fun t => if t = x then top.obj PUnit.unit else (hr (b t)).choose
  have ha (t : O) : r.obj (a t) = b t := by
    by_cases ht : t = x
    · subst t
      simpa only [a, ite_eq_left rfl] using hx
    · simpa only [a, ite_eq_right ht] using (hr (b t)).choose_spec
  let l := desc O a
  refine CommSq.HasLift.mk' ⟨l, ?_, ?_⟩
  · have hax : a x = top.obj PUnit.unit := by simp only [a, ite_eq_left rfl]
    exact (injection_desc O a x).trans
      ((congrArg BergnerObjects.select hax).trans (BergnerObjects.select_readback top))
  · have hb : r.obj ∘ a = b := funext ha
    exact (desc_comp O a r).trans
      ((congrArg (desc O) hb).trans (desc_readback O bottom))

/-- Every entire original free-point injection is a genuine global C0 cofibration. -/
theorem injection_cofibration (O : Type u) (x : O) : Bergner.cofibrations (injection O x) := by
  intro C D r hr
  exact injection_hasLiftingProperty O x r ((Bergner.generatingCofibrations_rlp_iff r).mp hr).1

end CategoryTheory.SimplicialEnrichment.BergnerFreeObjects
