/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

import MathlibExt.CategoryTheory.CategoryCohomology.RoosRightDerived

/-!
# Derived-limit comparison clients

These clients derive diagram-resolution availability from the coefficient
hypotheses, evaluate a limit projection of a Roos cycle, and compare the
Roos connecting map with the right-derived limit connecting map.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.CategoryCohomology

universe v₁ v₂ u₁ u₂

namespace RoosRightDerivedTests

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A] [Abelian A]
  [HasProducts.{max u₁ v₁} A] [AB4StarOfSize.{max u₁ v₁} A] [EnoughInjectives A]

local instance : HasLimitsOfShape I A := by
  let : HasLimitsOfSize.{max u₁ v₁, max u₁ v₁} A :=
    has_limits_of_hasEqualizers_and_products
  let : HasLimitsOfSize.{v₁, u₁} A := hasLimitsOfSizeShrink A
  infer_instance

local notation "Γ" => lim (J := I) (C := A)

local instance : Functor.PreservesZeroMorphisms Γ := inferInstance
local instance : Functor.Additive Γ := Functor.additive_of_preserves_binary_products Γ
local instance : EnoughInjectives (I ⥤ A) := enoughInjectives_functorCategory_of_products
local instance : HasInjectiveResolutions (I ⥤ A) := inferInstance

/-- A cycle keeps its actual coefficient under the derived-zero and native limit maps. -/
example (M : I ⥤ A) (i : I) :
    (roosComplex M).homologyπ 0 ≫
        (roosHomologyRightDerivedIso (I := I) (A := A) 0).hom.app M ≫
        (Functor.rightDerivedZeroIsoSelf Γ).hom.app M ≫ limit.π M i =
      (roosComplex M).iCycles 0 ≫ roosπ M (ComposableArrows.mk₀ (Opposite.op i)) := by
  have h := congr_app (roosHomologyRightDerivedIso_zero (I := I) (A := A)) M
  change (roosHomologyRightDerivedIso (I := I) (A := A) 0).hom.app M ≫
      (Functor.rightDerivedZeroIsoSelf Γ).hom.app M = (roosHomologyZeroIso M).hom at h
  let H : A := (roosComplex M).homology 0
  let Q : A := (Functor.rightDerived Γ 0).obj M
  let T : A := Functor.obj Γ M
  let π : (roosComplex M).cycles 0 ⟶ H := (roosComplex M).homologyπ 0
  let a : H ⟶ Q := (roosHomologyRightDerivedIso (I := I) (A := A) 0).hom.app M
  let b : Q ⟶ T := (Functor.rightDerivedZeroIsoSelf Γ).hom.app M
  let l : T ⟶ M.obj i := limit.π M i
  let c : H ⟶ T := (roosHomologyZeroIso M).hom
  have hab : a ≫ b = c := h
  have hs : π ≫ a ≫ b ≫ l = π ≫ (a ≫ b) ≫ l :=
    congrArg (fun k : H ⟶ M.obj i => π ≫ k) (Category.assoc a b l).symm
  have ht : π ≫ (a ≫ b) ≫ l = π ≫ c ≫ l :=
    congrArg (fun k : H ⟶ T => π ≫ k ≫ l) hab
  change π ≫ a ≫ b ≫ l = _
  exact hs.trans (ht.trans (roosHomologyπ_zeroIso_hom_π M i))

/-- An actual source morphism retains the native boundary without supplied derived data. -/
example (n : ℕ) (S : ShortComplex.ShortExactSequences (I ⥤ A)) {Z : A}
    (u : Z ⟶ (roosComplexFunctor.obj S.obj.X₃).homology n) :
    u ≫ (roosComplexFunctor_map_shortExact S.obj S.property).δ n (n + 1) (by rfl) ≫
        (roosHomologyRightDerivedIso (I := I) (A := A) (n + 1)).hom.app S.obj.X₁ =
      u ≫ (roosHomologyRightDerivedIso (I := I) (A := A) n).hom.app S.obj.X₃ ≫
        RightDerivedDelta.RDdelta Γ n S.obj S.property
          (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃) := by
  let H : A := (roosComplexFunctor.obj S.obj.X₃).homology n
  let T : A := (Functor.rightDerived Γ (n + 1)).obj S.obj.X₁
  have h : (roosComplexFunctor_map_shortExact S.obj S.property).δ n (n + 1) (by rfl) ≫
      (roosHomologyRightDerivedIso (I := I) (A := A) (n + 1)).hom.app S.obj.X₁ =
    (roosHomologyRightDerivedIso (I := I) (A := A) n).hom.app S.obj.X₃ ≫
      RightDerivedDelta.RDdelta Γ n S.obj S.property
        (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃) :=
    roosHomologyRightDerivedIso_connecting (I := I) (A := A) n S
  exact congrArg (fun f : H ⟶ T => u ≫ f) h

end RoosRightDerivedTests

end
