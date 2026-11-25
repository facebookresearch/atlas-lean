/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.LeftKanExtension
import Batteries.Tactic.Lint
import Lean

public section

namespace CategoryTheory.LeftKanAPITests

/-- All recorded public roots of the two defining producer modules. -/
def expectedProducerRoots : Array (Lean.Name × Array Lean.Name) := #[
  (`MathlibExt.CategoryTheory.Enriched.LeftKanExtension, #[
    `CategoryTheory.EnrichedFunctorCat.leftKanWeight,
    `CategoryTheory.EnrichedFunctorCat.leftKanWeight_eq,
    `CategoryTheory.EnrichedFunctorCat.leftKanWeight_obj,
    `CategoryTheory.EnrichedFunctorCat.leftKanCoendObject,
    `CategoryTheory.EnrichedFunctorCat.leftKanCoendActionComponent,
    `CategoryTheory.EnrichedFunctorCat.leftKanCoendActionComponent_eq,
    `CategoryTheory.EnrichedFunctorCat.leftKanCoendAction,
    `CategoryTheory.EnrichedFunctorCat.leftKanCoendAction_ι,
    `CategoryTheory.EnrichedFunctorCat.leftKanCoendMap,
    `CategoryTheory.EnrichedFunctorCat.leftKanCoendMap_uncurry,
    `CategoryTheory.EnrichedFunctorCat.leftKanCoendMap_id,
    `CategoryTheory.EnrichedFunctorCat.leftKanCoendMap_comp,
    `CategoryTheory.EnrichedFunctorCat.leftKanCoendFunctor,
    `CategoryTheory.EnrichedFunctorCat.leftKanCoendFunctor_obj,
    `CategoryTheory.EnrichedFunctorCat.leftKanCoendFunctor_map,
    `CategoryTheory.EnrichedFunctorCat.leftKanObject,
    `CategoryTheory.EnrichedFunctorCat.leftKanMapComponent,
    `CategoryTheory.EnrichedFunctorCat.leftKanMapComponent_ι,
    `CategoryTheory.EnrichedFunctorCat.leftKanMapComponent_id,
    `CategoryTheory.EnrichedFunctorCat.leftKanMapComponent_comp,
    `CategoryTheory.EnrichedFunctorCat.leftKanMap,
    `CategoryTheory.EnrichedFunctorCat.leftKanMap_component,
    `CategoryTheory.EnrichedFunctorCat.leftKan,
    `CategoryTheory.EnrichedFunctorCat.leftKan_obj,
    `CategoryTheory.EnrichedFunctorCat.leftKan_fullMap,
    `CategoryTheory.EnrichedFunctorCat.leftKanUnitComponent,
    `CategoryTheory.EnrichedFunctorCat.leftKanUnitComponent_action,
    `CategoryTheory.EnrichedFunctorCat.leftKanUnit,
    `CategoryTheory.EnrichedFunctorCat.leftKanUnit_component,
    `CategoryTheory.EnrichedFunctorCat.leftKanUnit_natural,
    `CategoryTheory.EnrichedFunctorCat.leftKanTransposeCocone,
    `CategoryTheory.EnrichedFunctorCat.leftKanTransposeCocone_eq,
    `CategoryTheory.EnrichedFunctorCat.leftKanTransposeMapComponent,
    `CategoryTheory.EnrichedFunctorCat.leftKanTransposeMapComponent_ι,
    `CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap,
    `CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap_component,
    `CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction,
    `CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction_component,
    `CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction_transpose,
    `CategoryTheory.EnrichedFunctorCat.leftKanTranspose_homToRestriction,
    `CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction_precomp,
    `CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction_postcomp,
    `CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv,
    `CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_apply,
    `CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_symm_apply,
    `CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_naturality_left,
    `CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_naturality_right,
    `CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_naturality_left_symm,
    `CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_naturality_right_symm,
    `CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction,
    `CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_homEquiv,
    `CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_unit,
    `CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_counit,
    `CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_unit_component,
    `CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_counit_ι,
    `CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_left_triangle,
    `CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_right_triangle,
    `CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap_unique,
    `CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap_unique_of_unit_components,
    `CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap_unique_of_generators,
    `CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_symm_ι,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_left_inverse,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_right_inverse,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_gradeFirstComponent,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_app,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_regrade,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_symm_regrade,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_presheaf_naturality,
    `CategoryTheory.EnrichedFunctorCat.leftKanEnrichedNatTransYonedaIso,
    `CategoryTheory.EnrichedFunctorCat.leftKanEnrichedNatTransYonedaIso_hom_app,
    `CategoryTheory.EnrichedFunctorCat.leftKanEnrichedNatTransYonedaIso_inv_app,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_symm_gradeFirstComponent_ι,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_unit_apply,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_unit,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_unit_symm_apply,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedGenerator_ext,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_symm_unique,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_left,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_right,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_left_symm,
    `CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_right_symm
  ]),
  (`MathlibExt.CategoryTheory.Enriched.ScalarCotensor, #[
    `CategoryTheory.EnrichedFunctor.cotensor,
    `CategoryTheory.EnrichedFunctor.cotensor_eq,
    `CategoryTheory.EnrichedFunctor.cotensor_map,
    `CategoryTheory.EnrichedFunctor.cotensor_doubleUncurry,
    `CategoryTheory.EnrichedFunctorCat.cotensorComponents_natural,
    `CategoryTheory.EnrichedFunctorCat.cotensorObject,
    `CategoryTheory.EnrichedFunctorCat.cotensorOfLeftComponents,
    `CategoryTheory.EnrichedFunctorCat.cotensorOfLeftComponents_component,
    `CategoryTheory.EnrichedFunctorCat.cotensorComponent,
    `CategoryTheory.EnrichedFunctorCat.cotensorComponent_naturality,
    `CategoryTheory.EnrichedFunctorCat.cotensorOfLeftComponents_reconstruct,
    `CategoryTheory.EnrichedFunctorCat.cotensorMap,
    `CategoryTheory.EnrichedFunctorCat.cotensorMap_component,
    `CategoryTheory.EnrichedFunctorCat.cotensor,
    `CategoryTheory.EnrichedFunctorCat.cotensorScalarMap,
    `CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_component,
    `CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_id,
    `CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_comp,
    `CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_naturality,
    `CategoryTheory.EnrichedFunctorCat.gradedToCotensor,
    `CategoryTheory.EnrichedFunctorCat.gradedToCotensor_component,
    `CategoryTheory.EnrichedFunctorCat.cotensorToGraded,
    `CategoryTheory.EnrichedFunctorCat.cotensorToGraded_app,
    `CategoryTheory.EnrichedFunctorCat.cotensorToGraded_gradeFirst,
    `CategoryTheory.EnrichedFunctorCat.cotensorToGraded_toCotensor,
    `CategoryTheory.EnrichedFunctorCat.gradedToCotensor_fromCotensor,
    `CategoryTheory.EnrichedFunctorCat.gradedCotensorEquiv,
    `CategoryTheory.EnrichedFunctorCat.gradedCotensorEquiv_apply,
    `CategoryTheory.EnrichedFunctorCat.gradedCotensorEquiv_symm_apply,
    `CategoryTheory.EnrichedFunctorCat.gradedToCotensor_precomp,
    `CategoryTheory.EnrichedFunctorCat.gradedToCotensor_postcomp,
    `CategoryTheory.EnrichedFunctorCat.cotensorToGraded_precomp,
    `CategoryTheory.EnrichedFunctorCat.cotensorToGraded_postcomp,
    `CategoryTheory.EnrichedFunctorCat.gradedToCotensor_regrade,
    `CategoryTheory.EnrichedFunctorCat.cotensorToGraded_regrade,
    `CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso,
    `CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_hom_component,
    `CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_inv_component,
    `CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_naturality,
    `CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_scalar_naturality
  ])
]

run_cmd do
  let env ← Lean.getEnv
  for (producer, roots) in expectedProducerRoots do
    let some idx := env.getModuleIdx? producer | throwError "producer module absent: {producer}"
    let mut count : Nat := 0
    for (name, _) in env.constants do
      if env.getModuleIdxFor? name == some idx then count := count + 1
    unless count > 0 do throwError "zero producer declarations: {producer}"
    for root in roots do
      unless (env.find? root).isSome do throwError "public root absent: {root}"
      unless env.getModuleIdxFor? root == some idx do
        throwError "public root has wrong defining module: {root}"
    Lean.logInfo m!"LEFT_KAN_MODULE {producer} COUNT {count} EXPECTED_ROOTS {roots.size}"

end CategoryTheory.LeftKanAPITests

#check CategoryTheory.EnrichedFunctorCat.leftKanWeight
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanWeight
#check CategoryTheory.EnrichedFunctorCat.leftKanWeight_eq
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanWeight_eq
#check CategoryTheory.EnrichedFunctorCat.leftKanWeight_obj
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanWeight_obj
#check CategoryTheory.EnrichedFunctorCat.leftKanCoendObject
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendObject
#check CategoryTheory.EnrichedFunctorCat.leftKanCoendActionComponent
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendActionComponent
#check CategoryTheory.EnrichedFunctorCat.leftKanCoendActionComponent_eq
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendActionComponent_eq
#check CategoryTheory.EnrichedFunctorCat.leftKanCoendAction
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendAction
#check CategoryTheory.EnrichedFunctorCat.leftKanCoendAction_ι
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendAction_ι
#check CategoryTheory.EnrichedFunctorCat.leftKanCoendMap
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendMap
#check CategoryTheory.EnrichedFunctorCat.leftKanCoendMap_uncurry
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendMap_uncurry
#check CategoryTheory.EnrichedFunctorCat.leftKanCoendMap_id
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendMap_id
#check CategoryTheory.EnrichedFunctorCat.leftKanCoendMap_comp
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendMap_comp
#check CategoryTheory.EnrichedFunctorCat.leftKanCoendFunctor
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendFunctor
#check CategoryTheory.EnrichedFunctorCat.leftKanCoendFunctor_obj
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendFunctor_obj
#check CategoryTheory.EnrichedFunctorCat.leftKanCoendFunctor_map
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendFunctor_map
#check CategoryTheory.EnrichedFunctorCat.leftKanObject
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanObject
#check CategoryTheory.EnrichedFunctorCat.leftKanMapComponent
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanMapComponent
#check CategoryTheory.EnrichedFunctorCat.leftKanMapComponent_ι
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanMapComponent_ι
#check CategoryTheory.EnrichedFunctorCat.leftKanMapComponent_id
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanMapComponent_id
#check CategoryTheory.EnrichedFunctorCat.leftKanMapComponent_comp
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanMapComponent_comp
#check CategoryTheory.EnrichedFunctorCat.leftKanMap
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanMap
#check CategoryTheory.EnrichedFunctorCat.leftKanMap_component
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanMap_component
#check CategoryTheory.EnrichedFunctorCat.leftKan
#print axioms CategoryTheory.EnrichedFunctorCat.leftKan
#check CategoryTheory.EnrichedFunctorCat.leftKan_obj
#print axioms CategoryTheory.EnrichedFunctorCat.leftKan_obj
#check CategoryTheory.EnrichedFunctorCat.leftKan_fullMap
#print axioms CategoryTheory.EnrichedFunctorCat.leftKan_fullMap
#check CategoryTheory.EnrichedFunctorCat.leftKanUnitComponent
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanUnitComponent
#check CategoryTheory.EnrichedFunctorCat.leftKanUnitComponent_action
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanUnitComponent_action
#check CategoryTheory.EnrichedFunctorCat.leftKanUnit
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanUnit
#check CategoryTheory.EnrichedFunctorCat.leftKanUnit_component
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanUnit_component
#check CategoryTheory.EnrichedFunctorCat.leftKanUnit_natural
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanUnit_natural
#check CategoryTheory.EnrichedFunctorCat.leftKanTransposeCocone
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeCocone
#check CategoryTheory.EnrichedFunctorCat.leftKanTransposeCocone_eq
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeCocone_eq
#check CategoryTheory.EnrichedFunctorCat.leftKanTransposeMapComponent
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeMapComponent
#check CategoryTheory.EnrichedFunctorCat.leftKanTransposeMapComponent_ι
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeMapComponent_ι
#check CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap
#check CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap_component
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap_component
#check CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction
#check CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction_component
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction_component
#check CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction_transpose
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction_transpose
#check CategoryTheory.EnrichedFunctorCat.leftKanTranspose_homToRestriction
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTranspose_homToRestriction
#check CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction_precomp
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction_precomp
#check CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction_postcomp
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction_postcomp
#check CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv
#check CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_apply
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_apply
#check CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_symm_apply
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_symm_apply
#check CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_naturality_left
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_naturality_left
#check CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_naturality_right
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_naturality_right
#check CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_naturality_left_symm
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_naturality_left_symm
#check CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_naturality_right_symm
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_naturality_right_symm
#check CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction
#check CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_homEquiv
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_homEquiv
#check CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_unit
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_unit
#check CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_counit
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_counit
#check CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_unit_component
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_unit_component
#check CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_counit_ι
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_counit_ι
#check CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_left_triangle
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_left_triangle
#check CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_right_triangle
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_right_triangle
#check CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap_unique
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap_unique
#check CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap_unique_of_unit_components
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap_unique_of_unit_components
#check CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap_unique_of_generators
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap_unique_of_generators
#check CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_symm_ι
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_symm_ι
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_left_inverse
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_left_inverse
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_right_inverse
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_right_inverse
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_gradeFirstComponent
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_gradeFirstComponent
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_app
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_app
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_regrade
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_regrade
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_symm_regrade
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_symm_regrade
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_presheaf_naturality
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_presheaf_naturality
#check CategoryTheory.EnrichedFunctorCat.leftKanEnrichedNatTransYonedaIso
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanEnrichedNatTransYonedaIso
#check CategoryTheory.EnrichedFunctorCat.leftKanEnrichedNatTransYonedaIso_hom_app
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanEnrichedNatTransYonedaIso_hom_app
#check CategoryTheory.EnrichedFunctorCat.leftKanEnrichedNatTransYonedaIso_inv_app
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanEnrichedNatTransYonedaIso_inv_app
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_symm_gradeFirstComponent_ι
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_symm_gradeFirstComponent_ι
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_unit_apply
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_unit_apply
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_unit
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_unit
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_unit_symm_apply
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_unit_symm_apply
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedGenerator_ext
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedGenerator_ext
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_symm_unique
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_symm_unique
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_left
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_left
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_right
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_right
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_left_symm
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_left_symm
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_right_symm
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_right_symm
#check CategoryTheory.EnrichedFunctor.cotensor
#print axioms CategoryTheory.EnrichedFunctor.cotensor
#check CategoryTheory.EnrichedFunctor.cotensor_eq
#print axioms CategoryTheory.EnrichedFunctor.cotensor_eq
#check CategoryTheory.EnrichedFunctor.cotensor_map
#print axioms CategoryTheory.EnrichedFunctor.cotensor_map
#check CategoryTheory.EnrichedFunctor.cotensor_doubleUncurry
#print axioms CategoryTheory.EnrichedFunctor.cotensor_doubleUncurry
#check CategoryTheory.EnrichedFunctorCat.cotensorComponents_natural
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorComponents_natural
#check CategoryTheory.EnrichedFunctorCat.cotensorObject
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorObject
#check CategoryTheory.EnrichedFunctorCat.cotensorOfLeftComponents
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorOfLeftComponents
#check CategoryTheory.EnrichedFunctorCat.cotensorOfLeftComponents_component
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorOfLeftComponents_component
#check CategoryTheory.EnrichedFunctorCat.cotensorComponent
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorComponent
#check CategoryTheory.EnrichedFunctorCat.cotensorComponent_naturality
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorComponent_naturality
#check CategoryTheory.EnrichedFunctorCat.cotensorOfLeftComponents_reconstruct
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorOfLeftComponents_reconstruct
#check CategoryTheory.EnrichedFunctorCat.cotensorMap
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorMap
#check CategoryTheory.EnrichedFunctorCat.cotensorMap_component
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorMap_component
#check CategoryTheory.EnrichedFunctorCat.cotensor
#print axioms CategoryTheory.EnrichedFunctorCat.cotensor
#check CategoryTheory.EnrichedFunctorCat.cotensorScalarMap
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorScalarMap
#check CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_component
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_component
#check CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_id
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_id
#check CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_comp
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_comp
#check CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_naturality
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_naturality
#check CategoryTheory.EnrichedFunctorCat.gradedToCotensor
#print axioms CategoryTheory.EnrichedFunctorCat.gradedToCotensor
#check CategoryTheory.EnrichedFunctorCat.gradedToCotensor_component
#print axioms CategoryTheory.EnrichedFunctorCat.gradedToCotensor_component
#check CategoryTheory.EnrichedFunctorCat.cotensorToGraded
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorToGraded
#check CategoryTheory.EnrichedFunctorCat.cotensorToGraded_app
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorToGraded_app
#check CategoryTheory.EnrichedFunctorCat.cotensorToGraded_gradeFirst
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorToGraded_gradeFirst
#check CategoryTheory.EnrichedFunctorCat.cotensorToGraded_toCotensor
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorToGraded_toCotensor
#check CategoryTheory.EnrichedFunctorCat.gradedToCotensor_fromCotensor
#print axioms CategoryTheory.EnrichedFunctorCat.gradedToCotensor_fromCotensor
#check CategoryTheory.EnrichedFunctorCat.gradedCotensorEquiv
#print axioms CategoryTheory.EnrichedFunctorCat.gradedCotensorEquiv
#check CategoryTheory.EnrichedFunctorCat.gradedCotensorEquiv_apply
#print axioms CategoryTheory.EnrichedFunctorCat.gradedCotensorEquiv_apply
#check CategoryTheory.EnrichedFunctorCat.gradedCotensorEquiv_symm_apply
#print axioms CategoryTheory.EnrichedFunctorCat.gradedCotensorEquiv_symm_apply
#check CategoryTheory.EnrichedFunctorCat.gradedToCotensor_precomp
#print axioms CategoryTheory.EnrichedFunctorCat.gradedToCotensor_precomp
#check CategoryTheory.EnrichedFunctorCat.gradedToCotensor_postcomp
#print axioms CategoryTheory.EnrichedFunctorCat.gradedToCotensor_postcomp
#check CategoryTheory.EnrichedFunctorCat.cotensorToGraded_precomp
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorToGraded_precomp
#check CategoryTheory.EnrichedFunctorCat.cotensorToGraded_postcomp
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorToGraded_postcomp
#check CategoryTheory.EnrichedFunctorCat.gradedToCotensor_regrade
#print axioms CategoryTheory.EnrichedFunctorCat.gradedToCotensor_regrade
#check CategoryTheory.EnrichedFunctorCat.cotensorToGraded_regrade
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorToGraded_regrade
#check CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso
#check CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_hom_component
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_hom_component
#check CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_inv_component
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_inv_component
#check CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_naturality
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_naturality
#check CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_scalar_naturality
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_scalar_naturality

#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.LeftKanExtension
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.ScalarCotensor
