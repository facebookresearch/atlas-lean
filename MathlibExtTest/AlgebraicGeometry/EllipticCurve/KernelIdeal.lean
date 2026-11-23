/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import MathlibExt.AlgebraicGeometry.EllipticCurve.KernelIdeal

open WeierstrassCurve

example {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [DecidableEq k]
    (W : WeierstrassCurve F) :
    (1 : rationalEndSubring k W) ∈ kernelIdealSet k W W (AddMonoidHom.id _) :=
  one_mem_kernelIdealSet_id k W
