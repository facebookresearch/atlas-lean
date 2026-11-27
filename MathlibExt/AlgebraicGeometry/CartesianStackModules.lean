/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackAffineModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Native cartesian stack modules and the good-moduli direct-image boundary

QCoh is the full category of all cartesian module presheaves on the actual
category of affine stack points. No finite-presentation restriction is imposed.
Pullback is literal precomposition along the native Grothendieck functor;
the ring maps are the actual maps of global sections. A direct image, when
used, is a right adjoint of that fixed functor. Its unit is the actual
adjunction unit, rather than an independently assigned structure-sheaf map.

The affine cartesian/QCoh dictionary and fppf direct-image construction are
completed source mathematics in AxiomMath/Stacks revision
c496df0d9beea9deaeabcea8492605f9a0a2313b (Apache License 2.0),
StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/QuasiCoherentCartesianEquivalence.lean
and Stacks/Quasicoherent/FppfModulesDirectImage.lean. The definitions here
provide their native carrier adapter; those source producers are not
reclassified as new mathematical gaps. See Alper, arXiv:0804.2242v3,
Definition 4.1, for the exactness and structure-sheaf conditions.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace AlgebraicGeometry.CartesianStackModules
open CategoryTheory CategoryTheory.Limits Opposite
open GeneralStackGeometry StackCycleGeometry StackFibreModels StackAffineModules

variable {S : Scheme.{0}}

abbrev QCoh (X : Stack S) :=
  (show ObjectProperty (ModulePresheaf X) from IsCartesian).FullSubcategory

def forget (X : Stack S) : QCoh X ⥤ ModulePresheaf X :=
  (show ObjectProperty (ModulePresheaf X) from IsCartesian).ι

/-- The map of affine points keeps the underlying scheme and its ring. -/
def affineMap {X Y : Stack S} (f : StackHom X Y) : AffinePoint X ⥤ AffinePoint Y where
  obj a := ⟨(totalMap f).obj a.obj, a.property⟩
  map h := ObjectProperty.homMk ((totalMap f).map h.hom)
  map_id _a := by apply ObjectProperty.hom_ext; exact (totalMap f).map_id _
  map_comp h k := by apply ObjectProperty.hom_ext; exact (totalMap f).map_comp _ _

/-- Literal reindexing of the actual module presheaf. -/
def presheafPullback {X Y : Stack S} (f : StackHom X Y) :
    ModulePresheaf Y ⥤ ModulePresheaf X :=
  PresheafOfModulesOfCommRing.pushforward₀ (affineMap f) (rings Y)

lemma presheafPullback_cartesian {X Y : Stack S} (f : StackHom X Y)
    (M : ModulePresheaf Y) (hM : IsCartesian M) :
    IsCartesian ((presheafPullback f).obj M) := by
  intro a b g N
  exact hM ((affineMap f).op.map g) N

def pullback {X Y : Stack S} (f : StackHom X Y) : QCoh Y ⥤ QCoh X where
  obj M := ⟨(presheafPullback f).obj M.obj,
    presheafPullback_cartesian f M.obj M.property⟩
  map h := ObjectProperty.homMk ((presheafPullback f).map h.hom)
  map_id _M := by apply ObjectProperty.hom_ext; exact (presheafPullback f).map_id _
  map_comp h k := by apply ObjectProperty.hom_ext; exact (presheafPullback f).map_comp _ _

/-- The unit module really has the scalar-extension universal property. -/
lemma unit_cartesian (X : Stack S) :
    IsCartesian (PresheafOfModulesOfCommRing.unit (rings X)) := by
  intro a b f N
  constructor
  · intro g h e
    have eone := LinearMap.congr_fun e (1 : (rings X).obj a)
    change g (((rings X).map f).hom 1) = h (((rings X).map f).hom 1) at eone
    have eh : g (1 : (rings X).obj b) = h (1 : (rings X).obj b) := by
      simpa only [map_one] using eone
    apply LinearMap.ext
    intro x
    change (rings X).obj b at x
    have hg := g.map_smul x (1 : (rings X).obj b)
    have hh := h.map_smul x (1 : (rings X).obj b)
    change g (x * (1 : (rings X).obj b)) = x • g (1 : (rings X).obj b) at hg
    change h (x * (1 : (rings X).obj b)) = x • h (1 : (rings X).obj b) at hh
    simpa only [mul_one] using hg.trans ((congrArg (x • ·) eh).trans hh.symm)
  · intro h
    refine ⟨LinearMap.toSpanSingleton ((rings X).obj b) N (h (1 : (rings X).obj a)), ?_⟩
    apply LinearMap.ext
    intro x
    change (rings X).obj a at x
    change ((rings X).map f).hom x • h (1 : (rings X).obj a) = h x
    have hh := h.map_smulₛₗ x (1 : (rings X).obj a)
    change h (x * (1 : (rings X).obj a)) = ((rings X).map f).hom x • h (1 : (rings X).obj a) at hh
    simpa only [mul_one] using hh.symm

def structureModule (X : Stack S) : QCoh X :=
  ⟨PresheafOfModulesOfCommRing.unit (rings X), unit_cartesian X⟩

/-- Fixed canonical pullback identifies the two actual structure modules. -/
def pullbackStructure {X Y : Stack S} (f : StackHom X Y) :
    (pullback f).obj (structureModule Y) ≅ structureModule X :=
  ObjectProperty.isoMk _ (PresheafOfModules.isoMk (fun _a => Iso.refl _)
    (by intro a b g; rfl))

/-- A chosen right adjoint to the fixed native QCoh pullback. This is an
implementation datum, not a claim of a new direct-image theorem. -/
structure DirectImage {X Y : Stack S} (f : StackHom X Y) where
  functor : QCoh X ⥤ QCoh Y
  adjunction : pullback f ⊣ functor

/-- The actual O_Y to f_* O_X map, normalized by the adjunction unit. -/
def DirectImage.structureMap {X Y : Stack S} {f : StackHom X Y}
    (D : DirectImage f) : structureModule Y ⟶ D.functor.obj (structureModule X) :=
  D.adjunction.unit.app (structureModule Y) ≫ D.functor.map (pullbackStructure f).hom

/-- Cohomological affineness and the actual O-unit condition only: this is the part of Alper's
good moduli space (arXiv:0804.2242v3, Defs. 3.1, 4.1, Rem. 4.4) checked here, without
quasi-compactness or an algebraic-space target. Finite-type, quasi-compactness and geometric
target hypotheses belong to each theorem. -/
def IsGood {X Y : Stack S} {f : StackHom X Y} (D : DirectImage f) : Prop :=
  D.functor.PreservesEpimorphisms ∧ IsIso D.structureMap

end AlgebraicGeometry.CartesianStackModules
