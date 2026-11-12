/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.IsingSpinMovingMesh

open StatMech.FrontierA

#print axioms finiteMarkedSpinCorrelation_nonneg
#print axioms finiteMarkedSpinCorrelation_relabel
#print axioms squareBoxMovingSpinCorrelation_nonneg
#print axioms squareBoxMovingSpinCorrelation_eq_of_relabel
#print axioms spinMeshRenormalization_uniformScale
#print axioms
  squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel
#print axioms
  tendsto_squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel
#print axioms deriv_inverseUniformScaleConformalMap
#print axioms spinConformalFactor_inverseUniformScaleConformalMap
#print axioms
  tendsto_squareBoxRenormalizedSpinCorrelation_inverseUniformScale_of_relabel
#print axioms squareBox_radius_eq_of_equiv
#print axioms squareBox_radiusSequence_eq_of_equiv
#print axioms squareBoxRenormalizedSpinCorrelation_eq_of_relabel
#print axioms
  squareBoxRenormalizedSpinCorrelation_transportError_eq_zero
