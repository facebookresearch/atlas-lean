/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.RestrictScalars

@[expose] public section
noncomputable section

open CategoryTheory

universe v uR uS

section Generic

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable (f : R →+* S) (hf : f.IsFinite)
variable (hp : @Module.Projective R _ S _ f.toModule)

example : (FGProjectiveCat.restrictScalars.{v} f hf hp).Additive := inferInstance

example : (FGProjectiveCat.restrictScalars.{v} f hf hp).IsExact := inferInstance

example {P Q : FGProjectiveCat.{v} S} (g : P ⟶ Q) (x : P) :
    (FGProjectiveCat.restrictScalars.{v} f hf hp).map g x = g x :=
  FGProjectiveCat.restrictScalars_map_apply f hf hp g x

example (P : FGProjectiveCat.{v} S) :
    ((FGProjectiveCat.restrictScalars.{v} f hf hp).obj P).obj =
      (ModuleCat.restrictScalars.{v} f).obj P.obj := by simp

end Generic

example (R : Type uR) [Ring R] :
    FGProjectiveCat.restrictScalars.{v} (RingHom.id R)
      RingHom.isFinite_id (FGProjectiveCat.projective_id R) ≅
        𝟭 (FGProjectiveCat.{v} R) :=
  FGProjectiveCat.restrictScalarsId R

private def diagonal : ℤ →+* ℤ × ℤ :=
  (RingHom.id ℤ).prod (RingHom.id ℤ)

private theorem diagonal_finite : diagonal.IsFinite := by
  exact (inferInstance : Module.Finite ℤ (ℤ × ℤ))

private theorem diagonal_projective :
    @Module.Projective ℤ _ (ℤ × ℤ) _ diagonal.toModule := by
  exact (inferInstance : Module.Projective ℤ (ℤ × ℤ))

/-- A genuine rank-two extension restricts its regular module with the
diagonal scalar action, rather than replacing the module by chosen data. -/
example (r : ℤ) (x : ℤ × ℤ) :
    r • (x : (FGProjectiveCat.restrictScalars diagonal diagonal_finite
      diagonal_projective).obj (FGProjectiveCat.of (R := ℤ × ℤ) (ℤ × ℤ))) =
      (r * x.1, r * x.2) := rfl

end
