/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.K0.RestrictScalars

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicKTheory

universe v uR uS

section Generic

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable (f : R →+* S) (hf : f.IsFinite)
variable (hp : @Module.Projective R _ S _ f.toModule)

example (P : FGProjectiveCat.{v} S) :
    RingK0.restrictScalars.{v} f hf hp (K0.mk P) =
      K0.mk ((FGProjectiveCat.restrictScalars.{v} f hf hp).obj P) := by simp

example (x y : K0 (FGProjectiveCat.{v} S)) :
    RingK0.restrictScalars.{v} f hf hp (x + y) =
      RingK0.restrictScalars.{v} f hf hp x + RingK0.restrictScalars.{v} f hf hp y := by simp

end Generic

/-- The common carrier universe remains independent of the ring universe. -/
example (R : Type uR) [Ring R] (x : K0 (FGProjectiveCat.{v} R)) :
    RingK0.restrictScalars.{v} (RingHom.id R) RingHom.isFinite_id
      (FGProjectiveCat.projective_id R) x = x := by simp

/-- At the original ring convention, the generic restriction has exactly
the original RingK0 domain and codomain. -/
example (R : Type uR) [Ring R] :
    RingK0 R →+ RingK0 R :=
  RingK0.restrictScalars (RingHom.id R) RingHom.isFinite_id (FGProjectiveCat.projective_id R)

end
