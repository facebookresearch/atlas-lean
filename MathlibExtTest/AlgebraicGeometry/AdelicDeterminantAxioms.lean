/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.GlobalBoundedDeterminantModels
import MathlibExt.AlgebraicGeometry.RationalAdelicModelMetrics
import MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights

/-! Integrity diagnostics for the computed actual determinant and metric maps.
The public import closure does not use Wanted declarations.
-/

#print axioms MathlibExt.AlgebraicGeometry.BoundedScalarDeterminants.component
#print axioms MathlibExt.AlgebraicGeometry.BoundedScalarDeterminants.determinantMap
#print axioms MathlibExt.AlgebraicGeometry.GlobalBoundedDeterminantModels.determinantTransition
#print axioms MathlibExt.AlgebraicGeometry.GlobalBoundedDeterminantModels.pairingTransition
#print axioms MathlibExt.AlgebraicGeometry.CompactificationMetricExtensions.placeOpenLine
#print axioms MathlibExt.AlgebraicGeometry.RationalAdelicModelMetrics.ModelSequence.class
#print axioms MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights.height_independent
