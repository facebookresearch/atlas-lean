/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.RestrictScalars
public import MathlibExt.Algebra.Category.FGProjectiveCat.BaseChange
public import MathlibExt.Algebra.Category.FGProjectiveCat.FiniteFreeComplement
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Restriction of a scalar extension with two coefficient coordinates

An actual coefficient-module equivalence `S ≃ₗ[R] R × R` distributes
through the native scalar-extension tensor product. Restriction of that
scalar extension is therefore isomorphic to the biproduct of two copies
of the original finite projective module.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe u

namespace FGProjectiveCat

variable {R S : Type u} [CommRing R] [CommRing S]
variable (f : R →+* S) (hf : f.IsFinite)
variable (hp : @Module.Projective R _ S _ f.toModule)
variable (eS : letI : Module R S := f.toModule; S ≃ₗ[R] R × R)

/-- The native scalar-extension tensor, restricted along the same actual
homomorphism, has the two original module coordinates. -/
def restrictScalarsBaseChangeProductEquiv (P : FGProjectiveCat.{u} R) :
    (restrictScalars f hf hp).obj ((baseChange f).obj P) ≃ₗ[R] P × P := by
  letI : Algebra R S := f.toAlgebra
  exact ((TensorProduct.congr eS (LinearEquiv.refl R P)).trans
    (TensorProduct.prodLeft R R R R P)).trans
      ((TensorProduct.lid R P).prodCongr (TensorProduct.lid R P))

/-- The coefficient coordinates act on every original pure tensor. -/
theorem restrictScalarsBaseChangeProductEquiv_tmul
    (P : FGProjectiveCat.{u} R) (s : S) (p : P) :
    restrictScalarsBaseChangeProductEquiv f hf hp eS P (s ⊗ₜ[R,f] p) =
      ((eS s).1 • p, (eS s).2 • p) := by
  rfl

/-- The actual restricted scalar extension is the original categorical
biproduct of two copies of the finite projective. -/
def restrictScalarsBaseChangeBiprodIso (P : FGProjectiveCat.{u} R) :
    (restrictScalars f hf hp).obj ((baseChange f).obj P) ≅ P ⊞ P :=
  isoOfLinearEquiv ((restrictScalarsBaseChangeProductEquiv f hf hp eS P).trans
    (biprodCarrierLinearEquiv P P).symm)

end FGProjectiveCat

end
