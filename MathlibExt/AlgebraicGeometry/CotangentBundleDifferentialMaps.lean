/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CotangentBundleTestModels

/-!
# The actual scheme map on cotangent bundles

The domain is the native scheme pullback of T*X along h. Its universal
covector is the actual pulled universal section. Applying the normalized
Kähler sheaf map and the total-space universal property defines dh on that
whole scheme, including nonreduced parameters. Cone images below use this
scheme map and the actual inverse image of the original closed subset.

Reference: Beilinson, arXiv:1505.06768v8, Section 1.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CotangentBundleDifferentialMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open AlgebraicDifferentialSheaves LocalDifferentialPullbacks GeneralModuleTotalSpaces
open CotangentBundleTestModels

variable {k : Type} [Field k] {X U : Over (Spec (.of k))}
  (BX : CotangentBundle X) (BU : CotangentBundle U) (h : U ⟶ X)
  (D : PullbackDifferential X h)

abbrev pullbackBundle : Scheme.{0} := pullback BX.projection h.left

/-- The full bundle differential is represented by the normalized sheaf differential. -/
def bundleDifferential : pullbackBundle BX h ⟶ BU.total :=
  let u : pullbackBundle BX h ⟶ U.left := pullback.snd BX.projection h.left
  let v := pulledSection (forms k X 1) BX.projection BX.universalSection
    (u ≫ h.left) (pullback.fst BX.projection h.left) pullback.condition
  BU.lift u (fibreMap D u v)

@[simp] theorem bundleDifferential_projection :
    bundleDifferential BX BU h D ≫ BU.projection = pullback.snd BX.projection h.left := by
  exact BU.lift_over _ _

/-- The actual set-theoretic dh image of C ×_X U, inside T*U. -/
def coneImage (C : ClosedCone X BX) : Set BU.total :=
  bundleDifferential BX BU h D '' (pullback.fst BX.projection h.left ⁻¹' C.support)

end MathlibExt.AlgebraicGeometry.CotangentBundleDifferentialMaps
