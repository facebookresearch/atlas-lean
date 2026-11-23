/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Ring.Comparison.ScalarExtensionK0Coefficients
import Mathlib.Topology.ContinuousMap.Algebra

/-! Coefficient clients of the original native scalar-extension map. -/

noncomputable section

open AlgebraicKTheory FGProjectiveCat

universe uR uS uT uX

variable {R : Type uR} {S : Type uS} {T : Type uT}
  [CommRing R] [CommRing S] [CommRing T]

example (f : R →+* S) :
    scalarExtensionK0 f (1 : RingK0 R) = (1 : RingK0 S) :=
  scalarExtensionK0_one f

example (f : R →+* S) (z : ℤ) :
    scalarExtensionK0 f (z : RingK0 R) = (z : RingK0 S) :=
  scalarExtensionK0_intCast f z

example (f : R →+* S) :
    scalarExtensionK0 f (-7 : RingK0 R) = (-7 : RingK0 S) := by
  simpa using scalarExtensionK0_intCast f (-7)

example (z : ℤ) : scalarExtensionK0 (RingHom.id R) (z : RingK0 R) = (z : RingK0 R) := by
  rw [scalarExtensionK0_id]
  rfl

example (f : R →+* S) (g : S →+* T) (z : ℤ) :
    ((scalarExtensionK0 g).comp (scalarExtensionK0 f)) (z : RingK0 R) = (z : RingK0 T) := by
  rw [← scalarExtensionK0_comp f g]
  exact scalarExtensionK0_intCast (g.comp f) z

-- The source function ring is neither assumed to be a field nor Noetherian.
example {X : Type uX} [TopologicalSpace X] [TopologicalSpace R] [IsTopologicalRing R]
    (x : X) (z : ℤ) :
    scalarExtensionK0
        ((Pi.evalRingHom (fun _ : X => R) x).comp ContinuousMap.coeFnRingHom)
        (z : RingK0 C(X, R)) =
      (z : RingK0 R) :=
  scalarExtensionK0_intCast _ z

#print axioms scalarExtensionK0_one
#print axioms scalarExtensionK0_intCast
