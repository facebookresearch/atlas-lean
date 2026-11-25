/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AlgebraicEquivariantCoefficientModels
public import MathlibExt.AlgebraicGeometry.IntegralChowChernModels
public import MathlibExt.Algebra.Module.EndScalarRestriction

/-!
# The actual fixed-action Chow comparison

The fixed scheme has the literal trivial torus action. Its quotient stack
projects to the scheme by descent of the actual invariant torsor map.
The comparison to ordinary Chow tensor Q[t,t^-1] is computed by this
native flat projection and the prescribed character-one coefficient.
Only bijectivity of that computed map is a shared theorem dependency.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.AlgebraicFixedChowModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open IntegralChowChernModels AlgebraicWeightBundleModels AlgebraicEquivariantChowModels
open EquivariantCharacterLineModels AlgebraicEquivariantCoefficientModels
open StackCycleRelations StackCycleGeometry StackChowGroups StackFibreModels
open scoped DirectSum TensorProduct

/-- The fixed action is the actual second projection on every scheme test. -/
@[instance_reducible] def trivialAction (X : Over base) : ModObj Gm X where
  smul := snd Gm X
  one_smul := by simp [CartesianMonoidalCategory.leftUnitor_hom]
  mul_smul := by simp

variable (F : SchemeData)
local instance : ModObj Gm F.scheme := trivialAction F.scheme
variable (D : CycleConstructionData base (FiniteTypeArtin ℂ)) (K : KreschPresentation D)

abbrev OrdinaryChow (i : ℤ) := TensorProduct ℤ ℚ (Chow F i)
abbrev GradedOrdinary := DirectSum ℤ (OrdinaryChow F)
abbrev FormalChow := TensorProduct ℚ Coefficients (GradedOrdinary F)

-- Native tensor/Chow conversions are large; cache the actual module instances.
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
instance ordinaryGroup (i : ℤ) : AddCommGroup (OrdinaryChow F i) :=
  inferInstanceAs (AddCommGroup (TensorProduct ℤ ℚ (Chow F i)))

-- The rational action is precisely the native scalar action on the same tensor.
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
instance ordinaryModule (i : ℤ) : Module ℚ (OrdinaryChow F i) :=
  inferInstanceAs (Module ℚ (TensorProduct ℤ ℚ (Chow F i)))

-- Cache the finite-dimensional grading indices' native direct-sum conversion.
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
instance gradedOrdinaryGroup : AddCommGroup (GradedOrdinary F) :=
  inferInstanceAs (AddCommGroup (DirectSum ℤ (OrdinaryChow F)))

-- This is the direct sum of the preceding native rational modules.
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
instance gradedOrdinaryModule : Module ℚ (GradedOrdinary F) :=
  inferInstanceAs (Module ℚ (DirectSum ℤ (OrdinaryChow F)))

/-- Projection to the ordinary represented scheme retains every original invariant map. -/
structure FixedChowData where
  quotient : EquivariantSource F.scheme
  schemeStack : Stack base
  inScope : FiniteTypeArtin ℂ schemeStack
  dictionary : SchemeCycleDictionary F schemeStack
  classes : CycleClassData D K schemeStack inScope
  comparison : SchemeComparisonData D K F schemeStack inScope dictionary classes
  bijective : ∀ i : ℤ, Function.Bijective (comparison.map i)
  projection : StackHom quotient.quotient.stack schemeStack
  descended : ∀ (T : Over base) (_q : quotient.quotient.stack.Fibre T), T ⟶ F.scheme
  descent_equation : ∀ (T : Over base) (q : quotient.quotient.stack.Fibre T),
    (((quotient.quotient.fibre T).functor.obj q).torsor.projection) ≫ descended T q =
      ((quotient.quotient.fibre T).functor.obj q).map
  pointComparison : ∀ (T : Over base) (q : quotient.quotient.stack.Fibre T),
    dictionary.comparison.functor.obj (point T ((component projection T).obj q)) ≅
      Over.mk (descended T q).left
  baseComparison : ∀ (T : Over base) (_q : quotient.quotient.stack.Fibre T),
    (dictionary.overBase.hom.app (point T ((component projection T).obj _q))).left =
      ((pointComparison T _q).hom).left
  pull : FlatChowPullData D K quotient.inScope inScope projection (-1)
  character : CharacterChernData quotient D K characterOne

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The inverse is the actual bijective scheme-cycle dictionary, before rational scalars. -/
def ordinarySchemeInverse (P : FixedChowData F D K) (i : ℤ) :
    Chow F i →+ ChowGroup D K P.schemeStack P.inScope i :=
  (AddEquiv.ofBijective (P.comparison.map i) (P.bijective i)).symm.toAddMonoidHom

-- The native scheme/Kresch coefficient comparison has a large dependent conversion.
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Ordinary integral cycles map by the native scheme dictionary inverse. -/
def ordinaryToEquivariant (P : FixedChowData F D K) (i : ℤ) :
    OrdinaryChow F i →ₗ[ℚ] EquivariantChow D K P.quotient i :=
  rationalMap ((chowRegrade D K P.quotient.quotient.stack P.quotient.inScope
    (show i+(-1)=i-1 by omega)).comp
      ((P.pull.map i).comp (ordinarySchemeInverse F D K P i)))

-- The source and target are native graded Kresch tensor modules.
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- All ordinary graded coefficients use the same computed projection pullback. -/
def gradedOrdinaryToEquivariant (P : FixedChowData F D K) :
    GradedOrdinary F →ₗ[ℚ] GradedChow P.quotient D K :=
  DirectSum.toModule ℚ ℤ (GradedChow P.quotient D K) (fun i =>
    (DirectSum.lof ℚ ℤ (EquivariantChow D K P.quotient) i).comp (ordinaryToEquivariant F D K P i))

-- Native scalar-extension instances retain the prescribed polynomial action.
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Laurent coefficients act on the actual native localized equivariant class. -/
def fixedChowComparison (P : FixedChowData F D K) :
    FormalChow F →ₗ[ℚ] LocalizedChow P.quotient D K P.character :=
  MathlibExt.EndScalarRestriction.tensorExtension
    (polynomialAction P.quotient D K P.character) (gradedOrdinaryToEquivariant F D K P)

/-- Bijectivity is a theorem about the computed character/flat-pull map. -/
def FixedChowIsomorphism (P : FixedChowData F D K) : Prop :=
  Function.Bijective (fixedChowComparison F D K P)

end MathlibExt.AlgebraicGeometry.AlgebraicFixedChowModels
