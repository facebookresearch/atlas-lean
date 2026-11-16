/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedDGModuli

/-!
# The actual DG-frame coefficient interval and its common induction unit

A whole moduli simplex supplies the actual curried coefficient-perfect
module on its original DG-frame term. The two endpoint maps and the
common degeneracy are the original cosimplicial maps, with their exact
split-retraction equation. Their enveloping maps fix all objects and
all homogeneous tensor generators.

Both endpoint unit maps restrict the same native enriched induction
unit along that degeneracy. The final restriction identification is
fixed on every module component by the original value equality. This
does not assume a strict natural transformation between arbitrary
DG-frame endpoint functors.

Source: Toen--Vaquie math/0503269v5, Section3.1 pp36--37, actual DG
mapping frames and module description; native enriched restriction and
induction sources retain their existing source notices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DGFrameCoefficientUnits

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open scoped Simplicial

universe u

variable {k : Type u} [CommRing k]

/-- The actual module value of every complete DG-mapping simplex, with all coefficient action maps. -/
def simplexBimodule {T : DGCat k} (F : DGFrame k (oppositeCategory T))
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N} (P : StrictPerfectSystem N S)
    (A : SAlg k) (n : SimplexCategory)
    (e : ((moduliFunctor F P).obj A).obj (op n)) :
    Bimodule k (F.diagram.obj n) (coefficientCategory N A) :=
  ⟨(e.comp (Cochains k) (P.realization A)).comp (Cochains k) (perfectToRaw (coefficientCategory N A))⟩

/-- The vertex specialization is the original native vertexBimodule. -/
theorem simplexBimodule_zero {T : DGCat k} (F : DGFrame k (oppositeCategory T))
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N} (P : StrictPerfectSystem N S)
    (A : SAlg k) (e : ((moduliFunctor F P).obj A) _⦋0⦌) :
    simplexBimodule F P A ⦋0⦌ e = vertexBimodule F P A e := rfl

/-- The simplex module is uncurried over its entire original source/coefficient envelope before replacement. -/
structure SimplexModulePoint {T : DGCat k} (F : DGFrame k (oppositeCategory T))
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N} (P : StrictPerfectSystem N S)
    (A : SAlg k) (n : SimplexCategory) (e : ((moduliFunctor F P).obj A).obj (op n)) where
  uncurried : EnvelopingModuleModel (simplexBimodule F P A n e)
  replacement : ModuleReplacement uncurried.module

/-- Both actual endpoint maps are retained as the original cosimplicial frame maps. -/
def frameEndpoint {T : DGCat k} (F : DGFrame k (oppositeCategory T)) (i : Fin 2) :
    F.diagram.obj ⦋0⦌ ⟶ F.diagram.obj ⦋1⦌ :=
  F.diagram.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)

/-- The common degeneracy is the original unique map [1] to [0]. -/
def frameRetraction {T : DGCat k} (F : DGFrame k (oppositeCategory T)) :
    F.diagram.obj ⦋1⦌ ⟶ F.diagram.obj ⦋0⦌ :=
  F.diagram.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)

/-- Both endpoints have the same exact source retraction. -/
theorem frameEndpoint_retraction {T : DGCat k} (F : DGFrame k (oppositeCategory T)) (i : Fin 2) :
    frameEndpoint F i ≫ frameRetraction F = 𝟙 (F.diagram.obj ⦋0⦌) := by
  have h : SimplexCategory.const ⦋0⦌ ⦋1⦌ i ≫ SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := by
    simp only [SimplexCategory.const_comp, SimplexCategory.const_apply, SimplexCategory.const_eq_id]
  rw [frameEndpoint, frameRetraction, ← _root_.CategoryTheory.Functor.map_comp, h]
  exact F.diagram.map_id _

section RestrictionIdentity

variable {A B : DGCat k} (f : A ⟶ B) (g : B ⟶ A) (h : f ≫ g = 𝟙 A)
  (Rf : RestrictionModel f) (Rg : RestrictionModel g)

include h in
/-- The actual composite restriction value is the original module value, using the same native split-retraction equation. -/
theorem restrictionCompositeValueEq (M : RightModule k A) (x : Aᵒᵖ) :
    (Rf.functor.obj (Rg.functor.obj M)).toEnrichedFunctor.obj x = M.toEnrichedFunctor.obj x := by
  rw [Rf.object_eq, Rg.object_eq]
  change M.toEnrichedFunctor.obj (op (g.obj (f.obj x.unop))) = M.toEnrichedFunctor.obj x
  have hx : g.obj (f.obj x.unop) = x.unop :=
    congrArg (fun q : A ⟶ A => q.obj x.unop) h
  exact congrArg (fun a => M.toEnrichedFunctor.obj (op a)) hx

/-- The source restriction comparison is fixed on every original coefficient component. -/
structure RestrictionCompositeIdentity where
  iso : ∀ M : RightModule k A, Rf.functor.obj (Rg.functor.obj M) ≅ M
  component_eq : ∀ (M : RightModule k A) (x : Aᵒᵖ),
    moduleComponent (iso M).hom x = eqToHom (restrictionCompositeValueEq f g h Rf Rg M x)

end RestrictionIdentity

section Interval

variable {T : DGCat k} (F : DGFrame k (oppositeCategory T))
  {N : ShuffleAlgebraFunctor k} (A : SAlg k)

/-- The same actual envelope is used on each original frame term. -/
def frameEnvelope (n : SimplexCategory) : DGCat k :=
  enveloping (F.diagram.obj n) (coefficientCategory N A)

/-- The envelope maps use exactly the source endpoint/degeneracy functors and the coefficient identity. -/
structure FrameEnvelopeRetraction where
  endpoint : ∀ i : Fin 2,
    TensorMapModel (A := oppositeCategory (F.diagram.obj ⦋0⦌))
      (B := oppositeCategory (F.diagram.obj ⦋1⦌))
      (C := coefficientCategory N A) (D := coefficientCategory N A)
      (EnrichedFunctor.op (V := Cochains k) (frameEndpoint F i))
      (𝟙 (coefficientCategory N A))
  retraction : TensorMapModel (A := oppositeCategory (F.diagram.obj ⦋1⦌))
    (B := oppositeCategory (F.diagram.obj ⦋0⦌))
    (C := coefficientCategory N A) (D := coefficientCategory N A)
    (EnrichedFunctor.op (V := Cochains k) (frameRetraction F))
    (𝟙 (coefficientCategory N A))
  commutes : ∀ i : Fin 2, (endpoint i).functor ≫ retraction.functor = 𝟙 (frameEnvelope F (N := N) A ⦋0⦌)

variable (B : FrameEnvelopeRetraction F (N := N) A)
  (R : RestrictionModel B.retraction.functor)
  (E : ExtensionModel B.retraction.functor R)
  (S : ∀ i : Fin 2, RestrictionModel (B.endpoint i).functor)
  (I : ∀ i : Fin 2, RestrictionCompositeIdentity (B.endpoint i).functor
    B.retraction.functor (B.commutes i) (S i) R)
  (M : DGDerivedModules k (frameEnvelope F (N := N) A ⦋1⦌))

/-- The common interval target is the original enriched induction of that same full projective one-simplex module. -/
def intervalInduction : RightModule k (frameEnvelope F (N := N) A ⦋0⦌) :=
  (E.functor.obj M).obj

/-- Both endpoint maps are native restrictions of the same actual enriched induction unit. -/
def endpointInductionUnit (i : Fin 2) : (S i).functor.obj M.obj ⟶ intervalInduction F A B R E M := by
  let a := (S i).functor.dgMap 0 (E.unit M)
  have ha : dgDifferential k 0 a = 0 := by
    rw [← (S i).functor.dgMap_dgDifferential, E.unit_closed, map_zero]
  exact (DGFunctor.homEquivDGCycles k _ _).symm ⟨a, (mem_dgCycles k).mpr ha⟩ ≫
    ((I i).iso (E.functor.obj M).obj).hom

end Interval

end MathlibExt.AlgebraicGeometry.DGFrameCoefficientUnits
