/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.DwyerKanVertexLifting
public import MathlibExt.AlgebraicTopology.SimplicialSet.MappingSpaceOppositeWeak
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.OppositeTrivialFibrations
public import MathlibExt.AlgebraicTopology.SimplicialSet.ContractibleFiber
public import MathlibExt.AlgebraicTopology.Quasicategory.Opposite
public import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral

/-!
# A genuine Dwyer–Kan categorical fibration is a trivial fibration

The original essential-surjectivity hypothesis gives strict vertex
lifting. Actual right-mapping weakness gives actual left-mapping weakness
for the opposite map. The proved left-fibration criterion and boundary
transposition then give every positive boundary lift. The whole opposite
equivalence transports the full boundary RLP back to the original map.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet
variable {X Y : SSet.{u}} {p : X ⟶ Y}

/-- A genuine categorical fibration into an original quasicategory which satisfies the actual Dwyer–Kan
  criterion has the full original boundary RLP. -/
theorem categoricalFibrations.mem_I_rlp_of_dwyerKan [Quasicategory Y]
    (hp : categoricalFibrations p) (hDK : isDwyerKanEquivalence p) :
    modelCategoryQuillen.I.rlp p := by
  let _ : InnerFibration p :=
    ((categoricalFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting p).mp hp).1
  let _ : Quasicategory X := quasicategory_of_innerFibration p
  let _ : Quasicategory Y.op := quasicategory_op Y
  let _ : InnerFibration (opFunctor.map p) := InnerFibration.op
  have hLeft : dwyerKanFullyFaithfulLeft (opFunctor.map p) := hDK.2.left_op
  have hTF : MappingSpaceLeftTrivialFibration (opFunctor.map p) :=
    mappingSpaceLeftTrivialFibration_of_dwyerKanFullyFaithfulLeft hLeft
  have hSurj : Function.Surjective (p.app (op ⦋0⦌)) :=
    hp.surjective_vertices_of_essSurj hDK.1
  have hSurjOp : Function.Surjective ((opFunctor.map p).app (op ⦋0⦌)) := by
    intro y
    obtain ⟨x, hx⟩ := hSurj (opObjEquiv y)
    refine ⟨opObjEquiv.symm x, ?_⟩
    apply opObjEquiv.injective
    simpa only [opFunctor_map, Equiv.apply_symm_apply] using hx
  have hOp : modelCategoryQuillen.I.rlp (opFunctor.map p) :=
    (modelCategoryQuillen_I_rlp_iff_hasLiftingProperty_boundary _).mpr (fun n => by
      cases n with
      | zero => exact hasLiftingProperty_boundary_zero_of_surjective_app_zero hSurjOp
      | succ n => exact hasLiftingProperty_boundary_succ_of_mappingSpaceLeftTrivialFibration hTF n)
  have hOpOp : modelCategoryQuillen.I.rlp (opFunctor.map (opFunctor.map p)) :=
    modelCategoryQuillen.op_map_mem_I_rlp _ hOp
  let e : Arrow.mk (opFunctor.map (opFunctor.map p)) ≅ Arrow.mk p :=
    Arrow.isoMk (opFunctorCompOpFunctorIso.app X) (opFunctorCompOpFunctorIso.app Y)
      (opFunctorCompOpFunctorIso.hom.naturality p).symm
  exact (modelCategoryQuillen.I.rlp.arrow_mk_iso_iff e).mp hOpOp

end SSet
