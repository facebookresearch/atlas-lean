/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryHoFibrationFiberKernel
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryStableIntegerHom
import Mathlib.Algebra.Exact.Basic

/-!
# Covariant original J-fiber group exactness at every source degree

The original κ-J fibration and caller pullback supply the actual covariant
fiber image law for every ordinary-Ho coefficient. Ordinary suspension
stability constructs the same additive Hom groups and identifies the
original source-built null maps with their actual zero elements. Canonical
composition homomorphisms therefore give exactness at every integer source
shift, with both source-map naturality squares retained.

The ordinary suspension-equivalence input is explicit. This proves the
original fiber/input position; the connecting positions and signed full
Puppe sequence still require the actual loop/fiber comparisons.
-/

set_option autoImplicit false
noncomputable section
universe w u v
open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OriginalOrdinaryHoFiberGroupExactness

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)
  [(DerivedSuspensionLoopAdjunction.suspension
    (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence]

local notation "N" => OriginalOrdinaryHoFibrationFiberKernel.null g Z hZ

/-- The original source-built null morphism is exactly the same actual ordinary-stable additive zero. -/
theorem null_eq_zero (T Y : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    N T Y = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  unfold OriginalOrdinaryHoFibrationFiberKernel.null
  have h : (GeneratedOrdinaryHoZero.isZero g Z hZ).isInitial.to Y = 0 :=
    (GeneratedOrdinaryHoZero.isZero g Z hZ).eq_zero_of_src _
  rw [h, comp_zero]

variable {X Y : HomotopyCategory C} (f : X ⟶ Y)
  (s : PullbackCone (OriginalOrdinaryHoFibrationSource.projection g f)
    (hZ.isInitial.to (OriginalOrdinaryHoArrowSource.targetObject g Y)))
  (hs : IsLimit s)

local notation "F" => OriginalOrdinaryHoFibrationFiberKernel.fiber g Z hZ f s
local notation "i" => OriginalOrdinaryHoFibrationFiberKernel.inclusion g Z hZ f s

/-- The original first fiber projection acts by the canonical actual additive postcomposition map. -/
def firstLeg (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (T ⟶ F) →+ (T ⟶ X) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.rightComp T i

/-- The full original input morphism acts on the same actual Hom groups. -/
def input (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (T ⟶ X) →+ (T ⟶ Y) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.rightComp T f

/-- The complete first-leg function is the unchanged original fiber inclusion word. -/
theorem firstLeg_apply (T : HomotopyCategory C) (l : T ⟶ F) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    firstLeg g Z hZ f s T l = l ≫ i := rfl

/-- The complete input function is postcomposition by the actual original Ho arrow. -/
theorem input_apply (T : HomotopyCategory C) (h : T ⟶ X) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    input g f T h = h ≫ f := rfl

include hs in
/-- Original J-fiber image exactness becomes actual group kernel/image exactness on every complete Ho coefficient. -/
theorem fiber_exact (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    Function.Exact (firstLeg g Z hZ f s T) (input g f T) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  intro h
  change h ≫ f = 0 ↔ ∃ l : T ⟶ F, l ≫ i = h
  rw [← null_eq_zero g Z hZ T Y]
  exact (OriginalOrdinaryHoFibrationFiberKernel.fiber_image_iff g Z hZ f s hs T h).symm

/-- Every actual source integer degree retains the same original ordinary shift of the coefficient. -/
abbrev hom (n : ℤ) (T E : HomotopyCategory C) :=
  (OrdinaryStableIntegerHom.shift g n).obj T ⟶ E

/-- The full original fiber leg is additive at each actual integer source shift. -/
def shiftedFirstLeg (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    hom g n T F →+ hom g n T X :=
  firstLeg g Z hZ f s ((OrdinaryStableIntegerHom.shift g n).obj T)

/-- The same original input morphism is additive at every integer source degree. -/
def shiftedInput (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    hom g n T X →+ hom g n T Y :=
  input g f ((OrdinaryStableIntegerHom.shift g n).obj T)

include hs in
/-- Every integer and every original coefficient retain the exact original covariant fiber/input group position. -/
theorem shifted_fiber_exact (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    Function.Exact (shiftedFirstLeg g Z hZ f s n T) (shiftedInput g f n T) :=
  fiber_exact g Z hZ f s hs ((OrdinaryStableIntegerHom.shift g n).obj T)

/-- The complete integer coefficient action uses the same actual ordinary shift on the original source map. -/
def coefficientMap (n : ℤ) {T T' : HomotopyCategory C} (a : T' ⟶ T) (E : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    hom g n T E →+ hom g n T' E := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.leftComp E ((OrdinaryStableIntegerHom.shift g n).map a)

/-- Every coefficient and source degree commute with the full original first fiber leg. -/
theorem shiftedFirstLeg_naturality (n : ℤ) {T T' : HomotopyCategory C} (a : T' ⟶ T) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (shiftedFirstLeg g Z hZ f s n T').comp (coefficientMap g n a F) =
      (coefficientMap g n a X).comp (shiftedFirstLeg g Z hZ f s n T) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  apply AddMonoidHom.ext
  intro l
  exact Category.assoc ((OrdinaryStableIntegerHom.shift g n).map a) l i

/-- Every coefficient and source degree commute with the complete original input map. -/
theorem shiftedInput_naturality (n : ℤ) {T T' : HomotopyCategory C} (a : T' ⟶ T) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (shiftedInput g f n T').comp (coefficientMap g n a X) =
      (coefficientMap g n a Y).comp (shiftedInput g f n T) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  apply AddMonoidHom.ext
  intro h
  exact Category.assoc ((OrdinaryStableIntegerHom.shift g n).map a) h f

include hs in
/-- Any specified original homotopy-generator family keeps all labels and integer covariant exactness tests. -/
theorem generator_fiber_exact {I : Type*} (G : I → HomotopyCategory C) (k : I) (n : ℤ) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    Function.Exact (shiftedFirstLeg g Z hZ f s n (G k)) (shiftedInput g f n (G k)) :=
  shifted_fiber_exact g Z hZ f s hs n (G k)

end HomotopicalAlgebra.OriginalOrdinaryHoFiberGroupExactness
