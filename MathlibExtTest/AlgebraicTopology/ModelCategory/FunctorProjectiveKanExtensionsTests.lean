/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.KanExtensions
import MathlibExtTest.AlgebraicTopology.ModelCategory.FunctorProjectiveDataTests
import MathlibExtTest.AlgebraicTopology.ModelCategory.CofibrantGenerationLeftKanExtensionsTests

/-!# Actual native Lan Quillen branches at the original independent data -/
set_option autoImplicit false
noncomputable section
universe uD vD uE vE uM vM wD wE
open CategoryTheory Functor Limits HomotopicalAlgebra

namespace MathlibExtTest.FunctorProjectiveKanExtensions

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {M : Type uM} [Category.{vM} M] [ModelCategory M]

section ExistingModels

variable (u : D ⥤ E) [∀ F : D ⥤ M, u.HasLeftKanExtension F]
  [ModelCategory (D ⥤ M)] [ModelCategory (E ⥤ M)]

example (hFD : fibrations (D ⥤ M) = (fibrations M).functorCategory D)
    (hFE : fibrations (E ⥤ M) = (fibrations M).functorCategory E)
    (hTD : trivialFibrations (D ⥤ M) = (trivialFibrations M).functorCategory D)
    (hTE : trivialFibrations (E ⥤ M) = (trivialFibrations M).functorCategory E) :
    (u.lanAdjunction M).IsQuillenAdjunction :=
  FunctorProjective.KanExtensions.isQuillen_of_pointwise_right_classes u hFD hFE hTD hTE

end ExistingModels

section FixedData

variable {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  {κE : Cardinal.{wE}} [Fact κE.IsRegular] [OrderBot κE.ord.ToType]
  [Small.{wD} D] [LocallySmall.{wD} D] [Small.{wE} E] [LocallySmall.{wE} E]
  [LocallySmall.{wD} E]
  (dD : CofibrantGenerationData M κD) (dE : CofibrantGenerationData M κE) (u : D ⥤ E)

example :
    letI : ∀ F : D ⥤ M, u.HasLeftKanExtension F := fun F => dD.hasLeftKanExtension u F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    (u.lanAdjunction M).IsQuillenAdjunction :=
  FunctorProjective.KanExtensions.isQuillen dD dE u

example {X Y : E ⥤ M} (p : X ⟶ Y) :
    letI : ∀ F : D ⥤ M, u.HasLeftKanExtension F := fun F => dD.hasLeftKanExtension u F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    fibrations (E ⥤ M) p →
      fibrations (D ⥤ M) (((whiskeringLeft D E M).obj u).map p) := by
  let _ : ∀ F : D ⥤ M, u.HasLeftKanExtension F := fun F => dD.hasLeftKanExtension u F
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  let _ : (u.lanAdjunction M).IsQuillenAdjunction :=
    FunctorProjective.KanExtensions.isQuillen dD dE u
  exact Adjunction.IsQuillenAdjunction.preservesFibrations (adj := u.lanAdjunction M) p

example {X Y : E ⥤ M} (p : X ⟶ Y) :
    letI : ∀ F : D ⥤ M, u.HasLeftKanExtension F := fun F => dD.hasLeftKanExtension u F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    trivialFibrations (E ⥤ M) p →
      trivialFibrations (D ⥤ M) (((whiskeringLeft D E M).obj u).map p) := by
  let _ : ∀ F : D ⥤ M, u.HasLeftKanExtension F := fun F => dD.hasLeftKanExtension u F
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  let _ : (u.lanAdjunction M).IsQuillenAdjunction :=
    FunctorProjective.KanExtensions.isQuillen dD dE u
  exact Adjunction.IsQuillenAdjunction.preservesTrivialFibrations (adj := u.lanAdjunction M) p

example {X Y : D ⥤ M} (i : X ⟶ Y) :
    letI : ∀ F : D ⥤ M, u.HasLeftKanExtension F := fun F => dD.hasLeftKanExtension u F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    cofibrations (D ⥤ M) i → cofibrations (E ⥤ M) (u.lan.map i) := by
  let _ : ∀ F : D ⥤ M, u.HasLeftKanExtension F := fun F => dD.hasLeftKanExtension u F
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  exact (FunctorProjective.KanExtensions.isQuillen dD dE u).preservesCofibrations i

example {X Y : D ⥤ M} (i : X ⟶ Y) :
    letI : ∀ F : D ⥤ M, u.HasLeftKanExtension F := fun F => dD.hasLeftKanExtension u F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    trivialCofibrations (D ⥤ M) i → trivialCofibrations (E ⥤ M) (u.lan.map i) := by
  let _ : ∀ F : D ⥤ M, u.HasLeftKanExtension F := fun F => dD.hasLeftKanExtension u F
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  exact (FunctorProjective.KanExtensions.isQuillen dD dE u).preservesTrivialCofibrations i

example (F : D ⥤ M) :
    letI : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dD.hasLeftKanExtension u H
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    IsCofibrant F → IsCofibrant (u.lan.obj F) := by
  let _ : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dD.hasLeftKanExtension u H
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  let _ : (u.lanAdjunction M).IsQuillenAdjunction :=
    FunctorProjective.KanExtensions.isQuillen dD dE u
  intro hF
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
    (adj := u.lanAdjunction M) hF

example (G : E ⥤ M) :
    letI : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dD.hasLeftKanExtension u H
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    IsFibrant G → IsFibrant (u ⋙ G) := by
  let _ : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dD.hasLeftKanExtension u H
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  let _ : (u.lanAdjunction M).IsQuillenAdjunction :=
    FunctorProjective.KanExtensions.isQuillen dD dE u
  intro hG
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects
    (adj := u.lanAdjunction M) hG

example (F : D ⥤ M) (d : D) :
    letI : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dD.hasLeftKanExtension u H
    letI : u.HasPointwiseLeftKanExtension F := dD.hasPointwiseLeftKanExtension u F
    ((u.lanAdjunction M).unit.app F).app d ≫
        (u.leftKanExtensionObjIsoColimit F (u.obj d)).hom =
      colimit.ι (CostructuredArrow.proj u (u.obj d) ⋙ F)
        (CostructuredArrow.mk (𝟙 (u.obj d))) := by
  let _ : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dD.hasLeftKanExtension u H
  let _ : u.HasPointwiseLeftKanExtension F := dD.hasPointwiseLeftKanExtension u F
  rw [u.lanAdjunction_unit M]
  exact leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom u F d

example (F : D ⥤ M) (e : E) (j : CostructuredArrow u e) :
    letI : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dD.hasLeftKanExtension u H
    letI : u.HasPointwiseLeftKanExtension F := dD.hasPointwiseLeftKanExtension u F
    colimit.ι (CostructuredArrow.proj u e ⋙ F) j ≫
        (u.leftKanExtensionObjIsoColimit F e).inv =
      (u.leftKanExtensionUnit F).app j.left ≫ (u.lan.obj F).map j.hom := by
  let _ : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dD.hasLeftKanExtension u H
  let _ : u.HasPointwiseLeftKanExtension F := dD.hasPointwiseLeftKanExtension u F
  exact ι_leftKanExtensionObjIsoColimit_inv u F e j

example {F G : D ⥤ M} (α : F ⟶ G) :
    letI : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dD.hasLeftKanExtension u H
    α ≫ (u.lanAdjunction M).unit.app G =
      (u.lanAdjunction M).unit.app F ≫ whiskerLeft u (u.lan.map α) := by
  let _ : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dD.hasLeftKanExtension u H
  exact (u.lanAdjunction M).unit.naturality α

example {G H : E ⥤ M} (β : G ⟶ H) :
    letI : ∀ F : D ⥤ M, u.HasLeftKanExtension F := fun F => dD.hasLeftKanExtension u F
    u.lan.map (whiskerLeft u β) ≫ (u.lanAdjunction M).counit.app H =
      (u.lanAdjunction M).counit.app G ≫ β := by
  let _ : ∀ F : D ⥤ M, u.HasLeftKanExtension F := fun F => dD.hasLeftKanExtension u F
  exact (u.lanAdjunction M).counit.naturality β

example (u₀ : Discrete PEmpty.{1} ⥤ E) :
    letI : ∀ F : Discrete PEmpty.{1} ⥤ M, u₀.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension u₀ F
    letI : ModelCategory (Discrete PEmpty.{1} ⥤ M) :=
      FunctorProjective.modelCategory.{wD} (J := Discrete PEmpty.{1}) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    (u₀.lanAdjunction M).IsQuillenAdjunction :=
  FunctorProjective.KanExtensions.isQuillen dD dE u₀

example (u₀ : Discrete ℕ ⥤ E) :
    letI : ∀ F : Discrete ℕ ⥤ M, u₀.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension u₀ F
    letI : ModelCategory (Discrete ℕ ⥤ M) :=
      FunctorProjective.modelCategory.{wD} (J := Discrete ℕ) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    (u₀.lanAdjunction M).IsQuillenAdjunction :=
  FunctorProjective.KanExtensions.isQuillen dD dE u₀

example (u₀ : SingleObj (Multiplicative ℕ) ⥤ E) :
    letI : ∀ F : SingleObj (Multiplicative ℕ) ⥤ M, u₀.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension u₀ F
    letI : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M) :=
      FunctorProjective.modelCategory.{wD} (J := SingleObj (Multiplicative ℕ)) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    (u₀.lanAdjunction M).IsQuillenAdjunction :=
  FunctorProjective.KanExtensions.isQuillen dD dE u₀

section Raised

local instance : Category.{vD} (ULift.{uD + 1} D) := uliftCategory D
local instance : Category.{max (vD + 1) vD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  @ULiftHom.category (ULift.{uD + 1} D) (inferInstance : Category.{vD} (ULift.{uD + 1} D))
local instance : Small.{wD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  small_map (ULiftHom.objEquiv.symm.trans Equiv.ulift)
local instance : LocallySmall.{wD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) where
  hom_small x y := by
    let _ : Small.{wD} (x.objDown.down ⟶ y.objDown.down) := LocallySmall.hom_small _ _
    exact small_map Equiv.ulift
local instance : Category.{vE} (ULift.{uE + 1} E) := uliftCategory E
local instance : Category.{max (vE + 1) vE} (ULiftHom.{vE + 1} (ULift.{uE + 1} E)) :=
  @ULiftHom.category (ULift.{uE + 1} E) (inferInstance : Category.{vE} (ULift.{uE + 1} E))
local instance : Small.{wE} (ULiftHom.{vE + 1} (ULift.{uE + 1} E)) :=
  small_map (ULiftHom.objEquiv.symm.trans Equiv.ulift)
local instance : LocallySmall.{wE} (ULiftHom.{vE + 1} (ULift.{uE + 1} E)) where
  hom_small x y := by
    let _ : Small.{wE} (x.objDown.down ⟶ y.objDown.down) := LocallySmall.hom_small _ _
    exact small_map Equiv.ulift
local instance : LocallySmall.{wD} (ULiftHom.{vE + 1} (ULift.{uE + 1} E)) where
  hom_small x y := by
    let _ : Small.{wD} (x.objDown.down ⟶ y.objDown.down) := LocallySmall.hom_small _ _
    exact small_map Equiv.ulift

example (u₀ : ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ ULiftHom.{vE + 1} (ULift.{uE + 1} E)) :
    letI : ∀ F : ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M, u₀.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension u₀ F
    letI : ModelCategory (ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M) :=
      FunctorProjective.modelCategory.{wD} (J := ULiftHom.{vD + 1} (ULift.{uD + 1} D)) dD
    letI : ModelCategory (ULiftHom.{vE + 1} (ULift.{uE + 1} E) ⥤ M) :=
      FunctorProjective.modelCategory.{wE} (J := ULiftHom.{vE + 1} (ULift.{uE + 1} E)) dE
    (u₀.lanAdjunction M).IsQuillenAdjunction :=
  FunctorProjective.KanExtensions.isQuillen dD dE u₀

end Raised
end FixedData
end MathlibExtTest.FunctorProjectiveKanExtensions
