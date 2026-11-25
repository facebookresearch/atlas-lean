/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GlobalFpPerfectionModels

/-!
# Native global perfection from the affine Frobenius direct-colimit source

The whole affine objects/maps and zero-stage projection are already
fixed. The global source extends them on every actual open chart,
retaining zero rings, empty schemes and the literal perfect-source
universal map. No Perf descent theorem is an input.

Source: Bhatt--Mathew1807.04725v4, Theorem5.16; Stacks perfection.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicGeometry.GlobalFpPerfectionModels

open FrobeniusPerfectionModels

/-- Glue the actual native affine direct-colimit perfections with their full scheme maps and projection. -/
def_wanted native_global_fp_perfection {p : ℕ} (F : FrobeniusSource p) : GlobalPerfectionSource F

end MathlibExt.AlgebraicGeometry.GlobalFpPerfectionModels
