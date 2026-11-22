/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryHoPuppeConnection
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryStableIntegerHom
import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryHoFiberGroupExactness
import MathlibExt.CategoryTheory.Preadditive.HomIso
import Mathlib.Algebra.Exact.Basic

/-!
# Original integer covariant Puppe group positions

The ordinary suspension-equivalence hypothesis is explicit. The same
original framing adjunction and its actual integer successor compare
degree n+1 maps into the target with degree n maps into its ordinary loops.

Canonical additive composition with the original connecting map, fibre
inclusion and input arrow gives two adjacent exact group positions at
every integer source degree and every original Ho coefficient. The same
chosen κ-J fibre and all specified generator labels are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v
open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OriginalOrdinaryIntegerPuppePositions

private def successorFromAdjunction {D : Type*} [Category* D] [Preadditive D]
    {L R : D ⥤ D} (adj : L ⊣ R) [L.Additive] (T T' E : D) (e : L.obj T ≅ T') :
    (T' ⟶ E) ≃+ (T ⟶ R.obj E) :=
  (Preadditive.HomIsoExact.homIso e.symm (Iso.refl E)).trans (adj.homAddEquiv T E)

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)
  [(DerivedSuspensionLoopAdjunction.suspension
    (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence]

local notation "Σ" => DerivedSuspensionLoopAdjunction.suspension (GeneratedFunctorialReplacements.fromGeneration g)
local notation "Ω" => DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)

/-- Every degree retains the actual integer SOURCE shift of the original coefficient. -/
abbrev hom (n : ℤ) (T E : HomotopyCategory C) :=
  (OrdinaryStableIntegerHom.shift g n).obj T ⟶ E

/-- The full original integer successor and actual additive ordinary adjunction compare the two source-degree Hom
groups. -/
def successorHomEquiv (n : ℤ) (T E : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    hom g (n + 1) T E ≃+ hom g n T ((Ω).obj E) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  let : (Σ).Additive := OrdinaryStableHoAdditive.suspension_additive g
  exact successorFromAdjunction
    (DerivedSuspensionLoopAdjunction.adjunction (GeneratedFunctorialReplacements.fromGeneration g))
    ((OrdinaryStableIntegerHom.shift g n).obj T) ((OrdinaryStableIntegerHom.shift g (n + 1)).obj T) E
    ((OrdinaryStableIntegerHom.successor g n).app T)

/-- The entire forward degree comparison is the actual original successor followed by the original Hom function. -/
theorem successorHomEquiv_apply (n : ℤ) (T E : HomotopyCategory C) (h : hom g (n + 1) T E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    successorHomEquiv g n T E h =
      (DerivedSuspensionLoopAdjunction.adjunction (GeneratedFunctorialReplacements.fromGeneration g)).homEquiv
        ((OrdinaryStableIntegerHom.shift g n).obj T) E
        ((OrdinaryStableIntegerHom.successor g n).hom.app T ≫ h) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  change (DerivedSuspensionLoopAdjunction.adjunction
    (GeneratedFunctorialReplacements.fromGeneration g)).homEquiv
      ((OrdinaryStableIntegerHom.shift g n).obj T) E
      ((OrdinaryStableIntegerHom.successor g n).hom.app T ≫ h ≫ 𝟙 E) = _
  rw [Category.comp_id]

/-- Every coefficient map retains the original full successor and ordinary Hom naturality square. -/
theorem successorHomEquiv_source (n : ℤ) {T T' : HomotopyCategory C} (a : T' ⟶ T)
    (E : HomotopyCategory C) (h : hom g (n + 1) T E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    successorHomEquiv g n T' E ((OrdinaryStableIntegerHom.shift g (n + 1)).map a ≫ h) =
      (OrdinaryStableIntegerHom.shift g n).map a ≫ successorHomEquiv g n T E h := by
  let := OrdinaryStableHoPreadditive.preadditive g
  rw [successorHomEquiv_apply, successorHomEquiv_apply]
  have hs := (OrdinaryStableIntegerHom.successor g n).hom.naturality a
  change (Σ).map ((OrdinaryStableIntegerHom.shift g n).map a) ≫
      (OrdinaryStableIntegerHom.successor g n).hom.app T =
    (OrdinaryStableIntegerHom.successor g n).hom.app T' ≫
      (OrdinaryStableIntegerHom.shift g (n + 1)).map a at hs
  rw [← Category.assoc, ← hs, Category.assoc]
  exact (DerivedSuspensionLoopAdjunction.adjunction
    (GeneratedFunctorialReplacements.fromGeneration g)).homEquiv_naturality_left _ _

/-- Every target map retains the actual original loop map in the full degree comparison. -/
theorem successorHomEquiv_target (n : ℤ) (T : HomotopyCategory C) {E E' : HomotopyCategory C}
    (a : E ⟶ E') (h : hom g (n + 1) T E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    successorHomEquiv g n T E' (h ≫ a) = successorHomEquiv g n T E h ≫ (Ω).map a := by
  let := OrdinaryStableHoPreadditive.preadditive g
  rw [successorHomEquiv_apply, successorHomEquiv_apply, ← Category.assoc]
  exact (DerivedSuspensionLoopAdjunction.adjunction
    (GeneratedFunctorialReplacements.fromGeneration g)).homEquiv_naturality_right _ _

variable (Z : C) (hZ : IsZero Z) {X Y : HomotopyCategory C} (f : X ⟶ Y)
  (s : PullbackCone (OriginalOrdinaryHoFibrationSource.projection g f)
    (hZ.isInitial.to (OriginalOrdinaryHoArrowSource.targetObject g Y)))
  (hs : IsLimit s)

local notation "F" => OriginalOrdinaryHoFibrationFiberKernel.fiber g Z hZ f s
local notation "i" => OriginalOrdinaryHoFibrationFiberKernel.inclusion g Z hZ f s
local notation "δ" => OriginalOrdinaryHoPuppeConnection.connecting g Z hZ f s hs
local notation "N" => OriginalOrdinaryHoFibrationFiberKernel.null g Z hZ

private theorem null_zero (T E : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    N T E = 0 :=
  OriginalOrdinaryHoFiberGroupExactness.null_eq_zero g Z hZ T E

/-- The actual original connecting map gives the additive boundary at every integer source degree. -/
def boundary (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    hom g (n + 1) T Y →+ hom g n T F := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact (Preadditive.rightComp ((OrdinaryStableIntegerHom.shift g n).obj T) δ).comp
    (successorHomEquiv g n T Y).toAddMonoidHom

/-- The full actual boundary function retains the original successor, Hom comparison and connecting word. -/
theorem boundary_apply (n : ℤ) (T : HomotopyCategory C) (h : hom g (n + 1) T Y) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    boundary g Z hZ f s hs n T h = successorHomEquiv g n T Y h ≫ δ := rfl

/-- The actual original fibre inclusion gives the same additive map at every integer source degree. -/
def firstLeg (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    hom g n T F →+ hom g n T X := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.rightComp ((OrdinaryStableIntegerHom.shift g n).obj T) i

/-- The actual caller Ho arrow gives the same additive map at every integer source degree. -/
def input (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    hom g n T X →+ hom g n T Y := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.rightComp ((OrdinaryStableIntegerHom.shift g n).obj T) f

/-- The boundary/fibre group position is exact for every integer and every full original Ho coefficient. -/
theorem boundary_exact (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    Function.Exact (boundary g Z hZ f s hs n T) (firstLeg g Z hZ f s n T) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  intro h
  change h ≫ i = 0 ↔ ∃ l : hom g (n + 1) T Y, successorHomEquiv g n T Y l ≫ δ = h
  have hImage :
      (∃ l : hom g (n + 1) T Y, successorHomEquiv g n T Y l ≫ δ = h) ↔
      (∃ l : hom g n T ((Ω).obj Y), l ≫ δ = h) := by
    constructor
    · rintro ⟨l, hl⟩
      exact ⟨successorHomEquiv g n T Y l, hl⟩
    · rintro ⟨l, hl⟩
      refine ⟨(successorHomEquiv g n T Y).symm l, ?_⟩
      simpa only [AddEquiv.apply_symm_apply] using hl
  rw [← null_zero g Z hZ ((OrdinaryStableIntegerHom.shift g n).obj T) X]
  exact (hImage.trans (OriginalOrdinaryHoPuppeConnection.connecting_image_iff g Z hZ f s hs
    ((OrdinaryStableIntegerHom.shift g n).obj T) h)).symm

include hs in
/-- The fibre/input group position is exact at every integer and the SAME original fibre and Ho arrow. -/
theorem fibre_exact (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    Function.Exact (firstLeg g Z hZ f s n T) (input g f n T) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  intro h
  change h ≫ f = 0 ↔ ∃ l : hom g n T F, l ≫ i = h
  rw [← null_zero g Z hZ ((OrdinaryStableIntegerHom.shift g n).obj T) Y]
  exact (OriginalOrdinaryHoFibrationFiberKernel.fiber_image_iff g Z hZ f s hs
    ((OrdinaryStableIntegerHom.shift g n).obj T) h).symm

/-- Every original coefficient map acts on the same constructed additive Hom groups. -/
def coefficientMap (n : ℤ) {T T' : HomotopyCategory C} (a : T' ⟶ T) (E : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    hom g n T E →+ hom g n T' E := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.leftComp E ((OrdinaryStableIntegerHom.shift g n).map a)

/-- The complete original successor and connecting map preserve every integer coefficient square. -/
theorem boundary_naturality (n : ℤ) {T T' : HomotopyCategory C} (a : T' ⟶ T) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (boundary g Z hZ f s hs n T').comp (coefficientMap g (n + 1) a Y) =
      (coefficientMap g n a F).comp (boundary g Z hZ f s hs n T) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  apply AddMonoidHom.ext
  intro h
  change successorHomEquiv g n T' Y ((OrdinaryStableIntegerHom.shift g (n + 1)).map a ≫ h) ≫ δ =
    (OrdinaryStableIntegerHom.shift g n).map a ≫ (successorHomEquiv g n T Y h ≫ δ)
  rw [successorHomEquiv_source]
  exact Category.assoc _ _ _

/-- The same original fibre leg retains every integer coefficient square. -/
theorem firstLeg_naturality (n : ℤ) {T T' : HomotopyCategory C} (a : T' ⟶ T) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (firstLeg g Z hZ f s n T').comp (coefficientMap g n a F) =
      (coefficientMap g n a X).comp (firstLeg g Z hZ f s n T) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  apply AddMonoidHom.ext
  intro h
  change ((OrdinaryStableIntegerHom.shift g n).map a ≫ h) ≫ i =
    (OrdinaryStableIntegerHom.shift g n).map a ≫ (h ≫ i)
  exact Category.assoc _ _ _

/-- The same full original input arrow retains every integer coefficient square. -/
theorem input_naturality (n : ℤ) {T T' : HomotopyCategory C} (a : T' ⟶ T) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (input g f n T').comp (coefficientMap g n a X) =
      (coefficientMap g n a Y).comp (input g f n T) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  apply AddMonoidHom.ext
  intro h
  change ((OrdinaryStableIntegerHom.shift g n).map a ≫ h) ≫ f =
    (OrdinaryStableIntegerHom.shift g n).map a ≫ (h ≫ f)
  exact Category.assoc _ _ _

/-- All specified original generator labels and all integer source degrees retain BOTH adjacent exact group positions.
-/
theorem generator_two_positions {I : Type*} (G : I → HomotopyCategory C) (k : I) (n : ℤ) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    Function.Exact (boundary g Z hZ f s hs n (G k)) (firstLeg g Z hZ f s n (G k)) ∧
      Function.Exact (firstLeg g Z hZ f s n (G k)) (input g f n (G k)) :=
  ⟨boundary_exact g Z hZ f s hs n (G k), fibre_exact g Z hZ f s hs n (G k)⟩

end HomotopicalAlgebra.OriginalOrdinaryIntegerPuppePositions
