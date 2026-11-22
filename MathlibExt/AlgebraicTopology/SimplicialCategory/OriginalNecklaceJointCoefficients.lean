/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceAmbientHom

/-!
# The SAME complete original joint-containing coefficient complex

The actual native necklace coefficient keeps EVERY original flag whose
first member contains its original joints. Faces and degeneracies retain
the same complete flag restriction. Its universal original flagged
object has the SAME entire native identity input and original endpoints.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace OriginalBead.TerminalFlag

/-- The SAME actual subcomplex of full original coefficients containing all original joints. -/
def coefficientComplex (T : Data) : (coefficientObject.{u} T.dimension).Subcomplex where
  obj q := {p | ∀ j ∈ T.joints, ULift.up.{u} j ∈ (p.obj 0).I}
  map θ p hp := by
    intro j hj
    exact (p.map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0)))).hom.down.down (hp j hj)

/-- The entire original joint coefficient simplicial set, retaining every original scalar flag. -/
abbrev fullCoefficient (T : Data) : SSet.{u} := coefficientComplex T

/-- Every SAME complete scalar coefficient keeps each joint in every original flag. -/
theorem coefficient_joint_all (T : Data) {q : SimplexCategoryᵒᵖ}
    (p : (fullCoefficient.{u} T).obj q) (t : Fin (q.unop.len + 1)) (j : Fin (T.dimension + 1))
    (hj : j ∈ T.joints) : ULift.up.{u} j ∈ (p.val.obj t).I :=
  (p.val.map (homOfLE (Fin.zero_le t))).hom.down.down (p.property j hj)

/-- The actual universal full flagged object has the SAME entire original native identity input. -/
def universalObject (T : Data) {q : SimplexCategoryᵒᵖ} (p : (fullCoefficient.{u} T).obj q) :
    OriginalFlaggedNecklace.Object T.object.{u} (sourceVertex T) (targetVertex T) q where
  necklace := T
  input := 𝟙 T.object
  source_eq := congrArg SSet.yonedaEquiv (Category.comp_id T.source)
  target_eq := congrArg SSet.yonedaEquiv (Category.comp_id T.target)
  coefficient := p.val
  joints := p.property

/-- The SAME universal flagged object retains its literal complete native source object. -/
theorem universalObject_necklace (T : Data) {q : SimplexCategoryᵒᵖ} (p : (fullCoefficient.{u} T).obj q) :
    (universalObject T p).necklace = T := rfl

/-- Every original full coefficient scalar operator retains its SAME actual coefficient restriction. -/
theorem fullCoefficient_map (T : Data) {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r)
    (p : (fullCoefficient.{u} T).obj q) :
    ((fullCoefficient T).map θ p).val = (coefficientObject T.dimension).map θ p.val := rfl

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
