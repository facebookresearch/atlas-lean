/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.RestrictScalars
public import MathlibExt.KTheory.Ring.K0.Projective

/-!
# Finite-projective restriction on algebraic K₀

For a finite unital homomorphism `R → S` with `S` projective as an
`R`-module, scalar restriction gives an additive transfer on the algebraic
K₀ of finite projectives. The map uses the actual restricted modules and
linear maps. No Noetherian hypothesis or Cartan inverse is needed.

The two ring universes are independent of the common module-carrier
universe. When these universes agree, the domain and codomain are the
original `RingK0 S` and `RingK0 R`.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe v uR uS

namespace AlgebraicKTheory.RingK0

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The additive K₀ transfer induced by the actual finite-projective
scalar-restriction functor in a common module-carrier universe. -/
def restrictScalars (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule) :
    K0 (FGProjectiveCat.{v} S) →+ K0 (FGProjectiveCat.{v} R) :=
  K0.map (FGProjectiveCat.restrictScalars.{v} f hf hp)

/-- Every generator maps to the class of its actual restricted module. -/
@[simp]
theorem restrictScalars_mk (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule) (P : FGProjectiveCat.{v} S) :
    restrictScalars.{v} f hf hp (K0.mk P) =
      K0.mk ((FGProjectiveCat.restrictScalars.{v} f hf hp).obj P) :=
  K0.map_mk _ P

/-- Identity restriction is the identity on the whole original K₀ group. -/
@[simp]
theorem restrictScalars_id (R : Type uR) [Ring R] :
    restrictScalars.{v} (RingHom.id R) RingHom.isFinite_id
      (FGProjectiveCat.projective_id R) =
        AddMonoidHom.id (K0 (FGProjectiveCat.{v} R)) := by
  unfold restrictScalars
  rw [K0.map_eq_of_iso (FGProjectiveCat.restrictScalarsId.{v} R)]
  exact K0.map_id

end AlgebraicKTheory.RingK0

end
