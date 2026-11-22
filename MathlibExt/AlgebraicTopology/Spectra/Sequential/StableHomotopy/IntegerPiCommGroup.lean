/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.IntegerPiCommutativity
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.ISuspensionIntegerPi

/-!
# The original integer stable functor takes values in commutative groups

The original cofibrant-replacement counit is an isomorphism on every
integer stable group. It transports the proved codiagonal commutativity
to every original spectrum, preserving the whole original group record
and each original functor map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerPiCommGroupGeometry

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev Index := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := Index.{u, v})

/-- The original replacement counit gives the same actual integer group isomorphism. -/
def qIso (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiFunctor.{u, v} q).obj (Q.obj X) ≅ (integerStablePiFunctor.{u, v} q).obj X :=
  (ISuspensionIntegerPiGeometry.qCounitIntegerNatIso (B := B) q).app X

/-- Every original integer stable group is commutative, without a cofibrancy assumption. -/
theorem mul_comm (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v})
    (a b : (integerStablePiFunctor.{u, v} q).obj X) : a * b = b * a := by
  let _ : IsCofibrant (Q.obj X) := Replacement.isCofibrant_cofibrantReplacement X
  let e := (qIso (B := B) q X).groupIsoToMulEquiv
  apply e.symm.injective
  exact (map_mul e.symm a b).trans
    ((IntegerPiCommutativityGeometry.mul_comm (B := B) (Q.obj X) q (e.symm a) (e.symm b)).trans
      (map_mul e.symm b a).symm)

/-- The original stable group has a commutative structure with all original operations retained. -/
@[instance_reducible]
def commGroup (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    CommGroup ((integerStablePiFunctor.{u, v} q).obj X) := by
  let g : Group ((integerStablePiFunctor.{u, v} q).obj X) := inferInstance
  exact { g with mul_comm := mul_comm (B := B) q X }

/-- The commutative structure retains the entire old group record. -/
theorem commGroup_toGroup (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (commGroup (B := B) q X).toGroup = inferInstanceAs (Group ((integerStablePiFunctor.{u, v} q).obj X)) := rfl

/-- The original integer stable object is bundled as a commutative group. -/
def object (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) : CommGrpCat.{v} :=
  @CommGrpCat.of ((integerStablePiFunctor.{u, v} q).obj X) (commGroup (B := B) q X)

/-- The original integer stable morphism is retained as the same commutative-group map. -/
def map (q : ℤ) {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    object (B := B) q X ⟶ object (B := B) q Y := by
  let _ := commGroup (B := B) q X
  let _ := commGroup (B := B) q Y
  exact CommGrpCat.ofHom ((integerStablePiFunctor.{u, v} q).map f).hom

/-- The whole commutative-group morphism has the original integer stable homomorphism. -/
theorem map_hom (q : ℤ) {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (map (B := B) q f).hom = ((integerStablePiFunctor.{u, v} q).map f).hom := rfl

/-- The actual original integer stable functor refines to commutative groups. -/
def functor (q : ℤ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤ CommGrpCat.{v} where
  obj := object (B := B) q
  map := map (B := B) q
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom ((integerStablePiFunctor.{u, v} q).map_id X) x
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom ((integerStablePiFunctor.{u, v} q).map_comp f g) x

/-- Forgetting commutativity retains the complete original stable-group object. -/
theorem object_forget (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (forget₂ CommGrpCat GrpCat).obj (object (B := B) q X) = (integerStablePiFunctor.{u, v} q).obj X := rfl

/-- Forgetting commutativity retains the entire original integer stable functor. -/
theorem functor_forget (q : ℤ) :
    functor (B := B) q ⋙ forget₂ CommGrpCat GrpCat = integerStablePiFunctor.{u, v} q := rfl

end PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerPiCommGroupGeometry
