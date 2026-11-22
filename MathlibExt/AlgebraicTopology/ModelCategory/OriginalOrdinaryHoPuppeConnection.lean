/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryJLoopComparison
import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryHoFibrationFiberKernel

/-!
# The actual ordinary Puppe connecting position on all Ho coefficients

The original Q/R representative of every full Ho arrow is factored by the
same original κ-J factory. Its caller-selected fibre keeps both limiting
projections. The original preimage isomorphism transports the derived
ordinary loop object to the actual original R target of that fibration.

The connecting image law is extended from cofibrant point-set coefficients
to every Ho coefficient through its actual original Q/preimage isomorphism.
The complete source-built null word is retained through the same original
source and target comparisons. The full connecting/fibre/input positions
therefore refer to one original Ho arrow and one caller-selected fibre.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v
open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OriginalOrdinaryHoPuppeConnection

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)

local notation "H" => toHomotopyCategory C
local notation "N" => OriginalOrdinaryHoFibrationFiberKernel.null g Z hZ

/-- The point-set covariant null word is exactly the same source-built ordinary Ho null word. -/
theorem pointNull_eq_hoNull (K B : C) :
    OriginalOrdinaryCovariantPuppeConnection.null Z hZ K B = N ((H).obj K) ((H).obj B) := by
  unfold OriginalOrdinaryCovariantPuppeConnection.null
  change (H).map (OrdinaryHoChosenFiberKernel.nullMap Z hZ K B) = _
  exact OriginalOrdinaryHoFibrationFiberKernel.null_image g Z hZ K B

variable [HasZeroObject C] [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]

local notation "Ω" => DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)

variable {X Y : HomotopyCategory C} (f : X ⟶ Y)
  (s : PullbackCone (OriginalOrdinaryHoFibrationSource.projection g f)
    (hZ.isInitial.to (OriginalOrdinaryHoArrowSource.targetObject g Y)))
  (hs : IsLimit s)

local instance originalProjectionFibration : Fibration (OriginalOrdinaryHoFibrationSource.projection g f) :=
  OriginalOrdinaryHoFibrationSource.projection_fibration g f

local notation "F" => OriginalOrdinaryHoFibrationFiberKernel.fiber g Z hZ f s
local notation "i" => OriginalOrdinaryHoFibrationFiberKernel.inclusion g Z hZ f s

/-- The whole original preimage Iso transports ordinary loops to the same actual original R target. -/
def loopPreimageIso (B : HomotopyCategory C) :
    (Ω).obj ((H).obj (OriginalOrdinaryHoArrowSource.preimage B)) ≅ (Ω).obj B :=
  (Ω).mapIso (OriginalOrdinaryHoArrowSource.preimageIso B)

/-- The actual ordinary connecting map retains the original loop preimage, κ-J fibration and same fibre. -/
def connecting : (Ω).obj Y ⟶ F := by
  let p := OriginalOrdinaryHoFibrationSource.projection g f
  let : Fibration p := OriginalOrdinaryHoFibrationSource.projection_fibration g f
  exact (loopPreimageIso g Y).inv ≫
    OriginalOrdinaryJLoopComparison.derivedConnectingToFiber Z hZ g
      (OriginalOrdinaryHoArrowSource.preimage Y) p s hs

/-- The complete connecting word consists of the same actual loop Iso inverse and original derived fibre map. -/
theorem connecting_eq :
    connecting g Z hZ f s hs =
      (loopPreimageIso g Y).inv ≫
        OriginalOrdinaryJLoopComparison.derivedConnectingToFiber Z hZ g
          (OriginalOrdinaryHoArrowSource.preimage Y)
          (OriginalOrdinaryHoFibrationSource.projection g f) s hs := by
  let : Fibration (OriginalOrdinaryHoFibrationSource.projection g f) :=
    OriginalOrdinaryHoFibrationSource.projection_fibration g f
  rfl

/-- Every ordinary-Ho coefficient retains the complete original connecting image/null-kernel law. -/
theorem connecting_image_iff (T : HomotopyCategory C) (h : T ⟶ F) :
    (∃ l : T ⟶ (Ω).obj Y, l ≫ connecting g Z hZ f s hs = h) ↔ h ≫ i = N T X := by
  let K := OriginalOrdinaryHoArrowSource.sourceObject g T
  let e := OriginalOrdinaryHoArrowSource.sourceIso g T
  let : IsCofibrant K := OriginalOrdinaryHoArrowSource.source_isCofibrant g T
  let p := OriginalOrdinaryHoFibrationSource.projection g f
  let : Fibration p := OriginalOrdinaryHoFibrationSource.projection_fibration g f
  let τ := loopPreimageIso g Y
  let δ := OriginalOrdinaryJLoopComparison.derivedConnectingToFiber Z hZ g
    (OriginalOrdinaryHoArrowSource.preimage Y) p s hs
  have hImage :
      (∃ l : T ⟶ (Ω).obj Y, l ≫ connecting g Z hZ f s hs = h) ↔
      (∃ l : (H).obj K ⟶ (Ω).obj ((H).obj (OriginalOrdinaryHoArrowSource.preimage Y)),
        l ≫ δ = e.hom ≫ h) := by
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨e.hom ≫ l ≫ τ.inv, ?_⟩
      have hh := congrArg (fun q => e.hom ≫ q) hl
      simpa only [connecting, τ, δ, p, Category.assoc] using hh
    · rintro ⟨l, hl⟩
      refine ⟨e.inv ≫ l ≫ τ.hom, ?_⟩
      change (e.inv ≫ l ≫ τ.hom) ≫ (τ.inv ≫ δ) = h
      rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, hl, Iso.inv_hom_id_assoc]
  have hBase := OriginalOrdinaryJLoopComparison.exact_at_fiber_from_loops Z hZ g
    (OriginalOrdinaryHoArrowSource.preimage Y) p s hs K (e.hom ≫ h)
  let a := OriginalOrdinaryHoFibrationSource.sourceIso g f
  let n := OriginalOrdinaryCovariantPuppeConnection.null Z hZ K
    (OriginalOrdinaryHoFibrationSource.sourceObject g f)
  have hNull : n ≫ a.hom = e.hom ≫ N T X := by
    dsimp only [n]
    rw [pointNull_eq_hoNull g Z hZ, OriginalOrdinaryHoFibrationFiberKernel.null_postcomp]
    exact (OriginalOrdinaryHoFibrationFiberKernel.null_precomp g Z hZ e.hom).symm
  have hKernel :
      (e.hom ≫ h) ≫ (H).map s.fst = n ↔ h ≫ i = N T X := by
    constructor
    · intro hk
      apply (cancel_epi e.hom).mp
      calc
        e.hom ≫ (h ≫ i) = ((e.hom ≫ h) ≫ (H).map s.fst) ≫ a.hom := by
          simp only [OriginalOrdinaryHoFibrationFiberKernel.inclusion, a, Category.assoc]
        _ = n ≫ a.hom := by rw [hk]
        _ = e.hom ≫ N T X := hNull
    · intro hk
      apply (cancel_mono a.hom).mp
      rw [hNull]
      have hh := congrArg (fun q => e.hom ≫ q) hk
      simpa only [OriginalOrdinaryHoFibrationFiberKernel.inclusion, a, Category.assoc] using hh
  exact hImage.trans (hBase.trans hKernel)

/-- Every full source-built null fibre projection admits an actual lift from the same derived ordinary loop object. -/
def connectingLift (T : HomotopyCategory C) (h : T ⟶ F) (hh : h ≫ i = N T X) :
    T ⟶ (Ω).obj Y :=
  Classical.choose ((connecting_image_iff g Z hZ f s hs T h).mpr hh)

/-- The whole connecting lift recovers the original caller's fibre map. -/
theorem connectingLift_fac (T : HomotopyCategory C) (h : T ⟶ F) (hh : h ≫ i = N T X) :
    connectingLift g Z hZ f s hs T h hh ≫ connecting g Z hZ f s hs = h :=
  Classical.choose_spec ((connecting_image_iff g Z hZ f s hs T h).mpr hh)

/-- The complete original connecting function is natural in every ordinary-Ho coefficient map. -/
theorem connecting_naturality {T T' : HomotopyCategory C} (a : T' ⟶ T) (l : T ⟶ (Ω).obj Y) :
    (a ≫ l) ≫ connecting g Z hZ f s hs = a ≫ (l ≫ connecting g Z hZ f s hs) :=
  Category.assoc _ _ _

/-- The same original fibre projection follows the actual connecting map by the source-built null word. -/
theorem connecting_inclusion :
    connecting g Z hZ f s hs ≫ i = N ((Ω).obj Y) X :=
  (connecting_image_iff g Z hZ f s hs ((Ω).obj Y) (connecting g Z hZ f s hs)).mp
    ⟨𝟙 _, Category.id_comp _⟩

/-- The entire original fibre/input image law and connecting/fibre image law use the same full Ho arrow and fibre. -/
theorem two_positions (T : HomotopyCategory C) :
    (∀ h : T ⟶ F, (∃ l : T ⟶ (Ω).obj Y, l ≫ connecting g Z hZ f s hs = h) ↔
      h ≫ i = N T X) ∧
    (∀ h : T ⟶ X, (∃ l : T ⟶ F, l ≫ i = h) ↔ h ≫ f = N T Y) :=
  ⟨connecting_image_iff g Z hZ f s hs T,
    OriginalOrdinaryHoFibrationFiberKernel.fiber_image_iff g Z hZ f s hs T⟩

/-- Every specified original coefficient family retains all original labels in both covariant image positions. -/
theorem generator_two_positions {I : Type*} (G : I → HomotopyCategory C) (k : I) :
    (∀ h : G k ⟶ F, (∃ l : G k ⟶ (Ω).obj Y, l ≫ connecting g Z hZ f s hs = h) ↔
      h ≫ i = N (G k) X) ∧
    (∀ h : G k ⟶ X, (∃ l : G k ⟶ F, l ≫ i = h) ↔ h ≫ f = N (G k) Y) :=
  two_positions g Z hZ f s hs (G k)

end HomotopicalAlgebra.OriginalOrdinaryHoPuppeConnection
