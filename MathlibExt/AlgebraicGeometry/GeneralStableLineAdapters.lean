/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
public import MathlibExt.AlgebraicGeometry.StableLineMaps

/-!
# Degree-one stable line maps as general stable-map families

The genus-zero one-pointed stable line families of `StableLineMaps` are general stable-map
families (`ofStableLine`), and their finite map automorphisms give geometric stability
(`ofStableLine_stable`). This adapter is split from `GeneralStableMapFamilies` so that the core
family API does not import bundle geometry or analytification.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.MarkedCurveStabilization

section ScopedAdapter

open MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
open MathlibExt.AlgebraicGeometry.PerverseSheaves

variable {r : ℕ}
  {X : ProjectiveBundle MathlibExt.AlgebraicGeometry.StableLineMaps.Point 0 r
    (MathlibExt.AlgebraicGeometry.StableLineMaps.targetGenerators r)}
  {T : ComplexScheme}

/-- The previous degree-one packet embeds into the general family contract. -/
def ofStableLine (F : MathlibExt.AlgebraicGeometry.StableLineMaps.StableLineFamily r X T) :
    Family X.projection.left 1 0 T.left T.hom :=
  ⟨F.curve, F.map, F.over⟩

theorem ofStableLine_stable
    (F : MathlibExt.AlgebraicGeometry.StableLineMaps.StableLineFamily r X T) :
    IsGeometricallyStable (ofStableLine F) := by
  intro Ω _ _ p
  let := F.stable Ω p
  let inclusion : geometricAutomorphisms (ofStableLine F) Ω p →
      MathlibExt.AlgebraicGeometry.StableLineMaps.mapAut r X F.curve F.map p :=
    fun e => ⟨e.val, e.property.1, e.property.2 0⟩
  exact Finite.of_injective inclusion (by
    intro a c h
    apply Subtype.ext
    exact congrArg
      (fun e : MathlibExt.AlgebraicGeometry.StableLineMaps.mapAut r X F.curve F.map p => e.val) h)

end ScopedAdapter

end MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
