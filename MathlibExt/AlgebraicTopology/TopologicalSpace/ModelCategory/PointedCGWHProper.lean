/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.UnderOverProperQuillen
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHProper
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHModelStructure

/-!
# Properness of pointed CGWH spaces

Importing the native CGWH properness instances together with the generic
Under-category properness theorem makes both properness classes available for
`PointedCGWH` inside the existing `CGWH.modelCategory` scope.  No adapter
instance or facade is needed.
-/
