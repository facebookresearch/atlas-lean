/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Condensed.SolidOverconvergentRHModels
import MathlibExt.Condensed.GlobalSolidCoefficientLimits
import MathlibExt.Condensed.DiamondEtaleCoefficientOperations
import MathlibExt.AlgebraicGeometry.AnalyticAdicDiamondification

/-! Proof-integrity diagnostics for actual source maps. These imports are
public definition modules; Wanted declarations do not enter this closure.
-/

#print axioms MathlibExt.AlgebraicGeometry.AnalyticAdicDiamondification.classComparison
#print axioms MathlibExt.Condensed.GlobalSolidCoefficientLimits.hyperdescentMap
#print axioms MathlibExt.Condensed.FrobeniusCoefficientUnit.geometricUnitMap
#print axioms MathlibExt.Condensed.FrobeniusCoefficientUnit.CompactUnit.linearization
#print axioms MathlibExt.Condensed.SolidOverconvergentRHModels.unitHomModule
#print axioms MathlibExt.Condensed.SolidOverconvergentRHModels.RHPModel.nerveMap
#print axioms MathlibExt.Condensed.DiamondEtaleCoefficientOperations.cochainUnit
#print axioms MathlibExt.CategoryTheory.CategoricalCoefficientLimits.comparisonLift_square
