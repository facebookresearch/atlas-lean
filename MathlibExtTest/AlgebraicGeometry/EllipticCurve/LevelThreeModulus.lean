/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import MathlibExt.AlgebraicGeometry.EllipticCurve.LevelThreeModulus

open WeierstrassCurve

example {R : Type*} [CommRing R] (α β : R) : (deuringCurve α β).Δ = β ^ 3 * (α ^ 3 - 27 * β) :=
  deuringCurve_Δ α β

example {F : Type*} [Field F] {τ ν : F} (hν : ν ≠ 0) :
    (deuringCurve τ ν).levelThreeModulus 0 0 ν = τ :=
  levelThreeModulus_deuringCurve hν

example {F : Type*} [Field F] {τ ν : F} (hν : ν ≠ 0) :
    (deuringCurve τ ν).levelThreeAbscissa 0 0 ν = ν :=
  levelThreeAbscissa_deuringCurve hν
