/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Condensed.PerfectoidIntegralVSites

/-!
# Untilting diagrams restrict integral rings functorially

The integral tilt rings of an untilting diagram restrict along a functorial ring map, which is
extended by the projected characteristic-`p` chart maps and commutes with `sharp`; the integral
coefficient restrictions are functorial too.
-/

namespace MathlibExtTest.PerfectoidIntegralVSites

open CategoryTheory
open MathlibExt.AlgebraicGeometry.AffinePerfectoidVSite
open MathlibExt.AlgebraicGeometry.PerfectoidSliceSites
open MathlibExt.AlgebraicGeometry.IntegralTiltModels
open MathlibExt.Condensed.PerfectoidIntegralVSites

variable {p : ℕ} [Fact p.Prime] {F : VSheaf p} (D : UntiltingDiagram p F)

example (T : AffineTest p F) (a : IntegralRing p (D.pair T)) : D.integral (𝟙 T) a = a := by
  rw [D.integral_id]
  rfl

example {T U V : AffineTest p F} (f : T ⟶ U) (g : U ⟶ V) (a : IntegralRing p (D.pair V)) :
    D.integral (f ≫ g) a = D.integral f (D.integral g a) := by
  rw [D.integral_comp]
  rfl

/-- The restriction of `sharp a` is `sharp` of the restricted integral element. -/
example {T U : AffineTest p F} (f : T ⟶ U) (a : IntegralRing p (D.pair U)) :
    (D.restriction f).hom (sharp p (D.pair U) (D := D.input U) a) =
      sharp p (D.pair T) (D := D.input T) (D.integral f a) :=
  D.sharp_integral f a

/-- The derived existential form of compatibility. -/
example {T U : AffineTest p F} (f : T ⟶ U) (a : IntegralRing p (D.pair U)) :
    ∃ b, (D.restriction f).hom (sharp p (D.pair U) (D := D.input U) a) =
      sharp p (D.pair T) (D := D.input T) b :=
  ⟨_, ((D.sharp_naturality f a).choose_spec).2⟩

/-- The integral coefficient restrictions are functorial. -/
example (T : AffineTest p F) (a : IntegralCoefficient D T) :
    integralRestriction D (𝟙 T) a = a := by
  apply ULift.ext
  apply Subtype.ext
  exact congrArg (fun q ↦ q a.down.1) (D.restriction_id T)

example {T U V : AffineTest p F} (f : T ⟶ U) (g : U ⟶ V) (a : IntegralCoefficient D V) :
    integralRestriction D (f ≫ g) a = integralRestriction D f (integralRestriction D g a) := by
  apply ULift.ext
  apply Subtype.ext
  exact congrArg (fun q ↦ q a.down.1) (D.restriction_comp f g)

end MathlibExtTest.PerfectoidIntegralVSites
