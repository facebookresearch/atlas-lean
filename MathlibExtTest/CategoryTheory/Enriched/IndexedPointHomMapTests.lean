/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.IndexedPointHomMap

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uC vC uJ

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace IndexedPointHomMapTests

section WholeIndexedMaps

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [Category.{vC} C] [EnrichedOrdinaryCategory V C]
  {J : Type uJ} [EnrichedCategory V J]
  (F : C ⥤ ForgetEnrichment V J) (index : C → J)
  (hobj : ∀ X, F.obj X = ForgetEnrichment.of V (index X))
  (m : ∀ X Y : C, (X ⟶[V] Y) ⟶ (index X ⟶[V] index Y))
  (hp : ∀ X Y : C,
    (fun f : X ⟶ Y => eHomEquiv V f ≫ m X Y) =
      (fun f : X ⟶ Y => ForgetEnrichment.homTo V (F.map f) ≫
        eqToHom (congrArg₂
          (fun P Q : ForgetEnrichment V J =>
            (ForgetEnrichment.to V P ⟶[V] ForgetEnrichment.to V Q))
              (hobj X) (hobj Y))))

example (X : C) : eId V X ≫ m X X = eId V (index X) :=
  UnitGeneratedEnrichment.map_id_of_index_point_function F index hobj m hp X

example (X : C) {Q : V} (r : (index X ⟶[V] index X) ⟶ Q) :
    eId V X ≫ m X X ≫ r = eId V (index X) ≫ r := by
  rw [← Category.assoc,
    UnitGeneratedEnrichment.map_id_of_index_point_function F index hobj m hp X]

variable [MonoidalClosed V] (hsep : IsSeparator (𝟙_ V))

example (X Y Z : C) : eComp V X Y Z ≫ m X Z =
    (m X Y ⊗ₘ m Y Z) ≫ eComp V (index X) (index Y) (index Z) :=
  UnitGeneratedEnrichment.map_comp_of_index_point_function F index hobj hsep m hp X Y Z

example (X Y Z : C) {Q : V} (r : (index X ⟶[V] index Z) ⟶ Q) :
    eComp V X Y Z ≫ m X Z ≫ r =
      (m X Y ⊗ₘ m Y Z) ≫ eComp V (index X) (index Y) (index Z) ≫ r := by
  rw [← Category.assoc, ← Category.assoc,
    UnitGeneratedEnrichment.map_comp_of_index_point_function F index hobj hsep m hp X Y Z]

end WholeIndexedMaps

section ActualPointFunctor

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [Category.{vC} C] [EnrichedOrdinaryCategory V C]

example (X : C) : eId V X ≫ 𝟙 (X ⟶[V] X) = eId V X := by
  let F := ForgetEnrichment.equivInverse V C
  let hobj : ∀ X : C, F.obj X = ForgetEnrichment.of V X := fun X => rfl
  let m : ∀ X Y : C, (X ⟶[V] Y) ⟶ (X ⟶[V] Y) := fun X Y => 𝟙 _
  have hp : ∀ X Y : C,
      (fun f : X ⟶ Y => eHomEquiv V f ≫ m X Y) =
        (fun f : X ⟶ Y => ForgetEnrichment.homTo V (F.map f) ≫
          eqToHom (congrArg₂
            (fun P Q : ForgetEnrichment V C =>
              (ForgetEnrichment.to V P ⟶[V] ForgetEnrichment.to V Q))
                (hobj X) (hobj Y))) := by
    intro X Y
    funext f
    dsimp only [F, hobj, m, ForgetEnrichment.equivInverse]
    rfl
  exact UnitGeneratedEnrichment.map_id_of_index_point_function F id hobj m hp X

variable [MonoidalClosed V] (hsep : IsSeparator (𝟙_ V))

example (X Y Z : C) : eComp V X Y Z ≫ 𝟙 (X ⟶[V] Z) =
    (𝟙 (X ⟶[V] Y) ⊗ₘ 𝟙 (Y ⟶[V] Z)) ≫ eComp V X Y Z := by
  let F := ForgetEnrichment.equivInverse V C
  let hobj : ∀ X : C, F.obj X = ForgetEnrichment.of V X := fun X => rfl
  let m : ∀ X Y : C, (X ⟶[V] Y) ⟶ (X ⟶[V] Y) := fun X Y => 𝟙 _
  have hp : ∀ X Y : C,
      (fun f : X ⟶ Y => eHomEquiv V f ≫ m X Y) =
        (fun f : X ⟶ Y => ForgetEnrichment.homTo V (F.map f) ≫
          eqToHom (congrArg₂
            (fun P Q : ForgetEnrichment V C =>
              (ForgetEnrichment.to V P ⟶[V] ForgetEnrichment.to V Q))
                (hobj X) (hobj Y))) := by
    intro A B
    funext f
    dsimp only [F, hobj, m, ForgetEnrichment.equivInverse]
    rfl
  exact UnitGeneratedEnrichment.map_comp_of_index_point_function F id hobj hsep m hp X Y Z

end ActualPointFunctor

end IndexedPointHomMapTests
