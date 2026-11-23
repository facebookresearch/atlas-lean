/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.Comparison.ScalarExtensionK0Coherence
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Integer coefficients of the original scalar-extension K₀ map

For commutative rings in independent universes, the existing additive map
`scalarExtensionK0` preserves the actual regular-module unit and integer
coefficients in the original `RingK0` groups. The unit calibration is the
existing regular-generator theorem; integer preservation then follows from
the general additive cast law.

No field or Noetherian premise is used. These laws therefore also apply to
scalar extension from ordinary continuous-function rings.

## References

* Weibel, *The K-book*, Chapter II, §2, p.68: the regular-module unit and
  scalar-extension functoriality of projective-module K₀.
-/

@[expose] public section

noncomputable section

open AlgebraicKTheory

universe uR uS

namespace FGProjectiveCat

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- The original native scalar-extension map preserves the K₀ ring unit,
independently of the two ring universes. -/
@[simp]
theorem scalarExtensionK0_one (f : R →+* S) :
    scalarExtensionK0 f (1 : RingK0 R) = (1 : RingK0 S) := by
  have hR : (K0.mk (FGProjectiveCat.of (R := R) R) : RingK0 R) = 1 :=
    K0.one_eq (FGProjectiveCat.{uR} R)
  have hS : (K0.mk (FGProjectiveCat.of (R := S) S) : RingK0 S) = 1 :=
    K0.one_eq (FGProjectiveCat.{uS} S)
  simpa only [hR, hS] using scalarExtensionK0_regular f

/-- The same original scalar-extension map preserves every integer cast.
The two native K₀ carrier universes remain independent. -/
@[simp]
theorem scalarExtensionK0_intCast (f : R →+* S) (z : ℤ) :
    scalarExtensionK0 f (z : RingK0 R) = (z : RingK0 S) :=
  map_intCast' (scalarExtensionK0 f) (scalarExtensionK0_one f) z

end FGProjectiveCat
