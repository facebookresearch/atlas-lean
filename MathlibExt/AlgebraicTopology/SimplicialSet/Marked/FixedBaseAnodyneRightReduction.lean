/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseHornRightReduction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterAssociativity
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# Original fixed-base horn right maps lift all native anodyne parameters

The actual whole mono/horn reduction gives a native Kan-fibration mapping
comparison. Every original Kan-anodyne scalar therefore lifts against
that same comparison. The original slice associator retains all boundary
corners of the fixed horn cells, so those actual corners belong to the
original generated small left class. No weak-class or model outcome is
assumed, and the supplied marked codomain may be arbitrary.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty MonoidalCategory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Marked

/-- The original Cartesian small right class lifts every native anodyne scalar/marked-mono corner. -/
theorem cartesianFixedBaseRight_anodyne_lifting {B : SSet.{u}} {E F X X' : Over (max B)}
    (p : E ⟶ F) (hp : (cartesianFixedBaseCells B).rlp p) (i : X ⟶ X') [Mono i]
    {K L : SSet.{u}} (a : K ⟶ L) (ha : anodyneExtensions a) :
    HasLiftingProperty (overParameterPushoutProduct a i) p := by
  let q := overParameterMappingComparison i p
  have hq : Fibration q := (overParameterHorn_lifting_iff i p).mp
    (cartesianFixedBaseRight_horn_lifting p hp i)
  have hr : modelCategoryQuillen.J.{u}.rlp q := (modelCategoryQuillen.fibration_iff _).mp hq
  have hl : HasLiftingProperty a q := by
    rw [anodyneExtensions_eq_llp_rlp] at ha
    exact ha _ hr
  exact (overParameterPushoutProduct_hasLiftingProperty_iff a i p).mpr hl

/-- The original dual small right class has the same full native Kan-anodyne/mono lifting law. -/
theorem cocartesianFixedBaseRight_anodyne_lifting {B : SSet.{u}} {E F X X' : Over (max B)}
    (p : E ⟶ F) (hp : (cocartesianFixedBaseCells B).rlp p) (i : X ⟶ X') [Mono i]
    {K L : SSet.{u}} (a : K ⟶ L) (ha : anodyneExtensions a) :
    HasLiftingProperty (overParameterPushoutProduct a i) p := by
  let q := overParameterMappingComparison i p
  have hq : Fibration q := (overParameterHorn_lifting_iff i p).mp
    (cocartesianFixedBaseRight_horn_lifting p hp i)
  have hr : modelCategoryQuillen.J.{u}.rlp q := (modelCategoryQuillen.fibration_iff _).mp hq
  have hl : HasLiftingProperty a q := by
    rw [anodyneExtensions_eq_llp_rlp] at ha
    exact ha _ hr
  exact (overParameterPushoutProduct_hasLiftingProperty_iff a i p).mpr hl

/-- Every actual original Cartesian fixed-base horn cell retains its whole scalar boundary corners in the
  original generated small left class. -/
theorem fixedBaseHornCell_cartesian_boundary_left (B : SSet.{u})
    (s : FixedBaseMonoIndex B × FixedBaseHornIndex) (n : ℕ) :
    (cartesianFixedBaseCells B).rlp.llp (overParameterPushoutProduct (boundary.{u} n).ι (fixedBaseHornCell B
      s).hom) := by
  intro E F p hp
  let i := (fixedBaseMonoCell B s.1).hom
  let _ : Mono i := fixedBaseMonoCell_mono B s.1
  let a := (horn.{u} (s.2.1 + 1) s.2.2).ι
  let q := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (boundary.{u} n).ι a
  have hq : anodyneExtensions q.ι := anodyneExtensions_pushoutObjObjι q (anodyneExtensions.horn_ι s.2.2)
  have h := cartesianFixedBaseRight_anodyne_lifting p hp i q.ι hq
  exact (HasLiftingProperty.iff_of_arrow_iso_left
    (overParameterPushoutProductAssociativityIso (boundary.{u} n).ι a i) p).mpr h

/-- The original dual fixed-base horn cells have the same entire scalar boundary-corner left membership. -/
theorem fixedBaseHornCell_cocartesian_boundary_left (B : SSet.{u})
    (s : FixedBaseMonoIndex B × FixedBaseHornIndex) (n : ℕ) :
    (cocartesianFixedBaseCells B).rlp.llp (overParameterPushoutProduct (boundary.{u} n).ι (fixedBaseHornCell
      B s).hom) := by
  intro E F p hp
  let i := (fixedBaseMonoCell B s.1).hom
  let _ : Mono i := fixedBaseMonoCell_mono B s.1
  let a := (horn.{u} (s.2.1 + 1) s.2.2).ι
  let q := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (boundary.{u} n).ι a
  have hq : anodyneExtensions q.ι := anodyneExtensions_pushoutObjObjι q (anodyneExtensions.horn_ι s.2.2)
  have h := cocartesianFixedBaseRight_anodyne_lifting p hp i q.ι hq
  exact (HasLiftingProperty.iff_of_arrow_iso_left
    (overParameterPushoutProductAssociativityIso (boundary.{u} n).ι a i) p).mpr h

end SSet.Marked
