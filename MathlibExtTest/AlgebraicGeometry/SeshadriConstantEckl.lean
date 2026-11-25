/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.SeshadriConstantEckl

open MathlibExt.AlgebraicGeometry.SeshadriConstant
open MathlibExt.AlgebraicGeometry.SeshadriConstantWanted

example : (4 / 13 : ℝ) ≤ seshadriConstant10 :=
  eckl2008LowerBound_wanted
