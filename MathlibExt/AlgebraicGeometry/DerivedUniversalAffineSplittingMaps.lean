/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedSplittingDifferentialModels
public import MathlibExt.AlgebraicGeometry.DerivedAffineFamilies

/-!
# The full affine mapping parameter and its universal splitting action

The parameter is the native mapping simplicial set Map(Spec(A),F).
Every parameter simplex is an actual compatible algebra/simplex family.
Evaluation applies that family to the actual algebra mapping simplex.
Its algebra naturality identifies evaluation on every strict splitting
with F applied to that splitting. No restriction to point charts or to
isomorphism classes is made.

The universal derivation map is the native map of homotopy pullbacks
of this evaluation square, over the entire mapping parameter. The same
endpoint and diagonal path map is retained at every coefficient test.
Cotangent transposition and its coherent exterior diagram are separate
source construction requests.

Sources: PTVV arXiv:1111.3209v4, Section 1.2 and Proposition 1.14;
HAG II arXiv:math/0404373v7, Sections 1.3.7 and 1.4.1. The native
enriched Hom, algebra replacement and Kan path notices remain in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedUniversalAffineSplittingMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.SimplicialHomotopyLimits
open MathlibExt.AlgebraicGeometry.AffineSplittingCotangentActions
open MathlibExt.AlgebraicGeometry.DerivedSplittingDifferentialModels
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]

/-- The entire native affine mapping space, including all its gauge simplices. -/
def affineParameters (Q : AlgebraReplacementFunctor k) (F : Prestack k) (A : SAlg k) :
    SSet.{u + 1} :=
  DerivedPrestackMapping.mapping k (affineMapping k Q A) F

/-- The actual native affine mapping functor in every coefficient algebra. -/
def affineParameterPrestack (Q : AlgebraReplacementFunctor k) (F : Prestack k) : Prestack k :=
  (opOpEquivalence (SAlg k)).inverse ⋙ (affineYoneda k Q).op ⋙
    (mappingBifunctor k).flip.obj F

/-- Its value is exactly the same full parameter simplicial set. -/
theorem affineParameterPrestack_obj (Q : AlgebraReplacementFunctor k) (F : Prestack k)
    (A : SAlg k) : (affineParameterPrestack Q F).obj A = affineParameters Q F A := rfl

/-- Evaluation of the actual compatible parameter family on an actual algebra mapping simplex. -/
def evaluationAt (Q : AlgebraReplacementFunctor k) (F : Prestack k) (A B : SAlg k) :
    ((affineMapping k Q A).obj B) ⊗ affineParameters Q F A ⟶ F.obj B where
  app n := ↾fun p => ((p.2.app n (𝟙 n)).app B) p.1
  naturality n m f := by
    ext p
    exact congrArg (fun t => (t.app B) p.1) (p.2.naturality f (𝟙 n))

/-- Algebra transport commutes with that same whole native parameter map. -/
theorem evaluationAt_naturality (Q : AlgebraReplacementFunctor k) (F : Prestack k)
    (A : SAlg k) {B C : SAlg k} (f : B ⟶ C) :
    ((affineMapping k Q A).map f ⊗ₘ 𝟙 (affineParameters Q F A)) ≫ evaluationAt Q F A C =
      evaluationAt Q F A B ≫ F.map f := by
  ext n p
  exact congrArg (fun t => t p.1) ((p.2.app n (𝟙 n)).naturality f)

/-- The literal universal affine family, with the whole mapping parameter held as a constant prestack. -/
def universalDomain (Q : AlgebraReplacementFunctor k) (F : Prestack k) (A : SAlg k) :
    Prestack k :=
  affineMapping k Q A ⊗ (Functor.const (SAlg k)).obj (affineParameters Q F A)

/-- This actual universal prestack map retains every mapping and gauge simplex. -/
def universalEvaluation (Q : AlgebraReplacementFunctor k) (F : Prestack k) (A : SAlg k) :
    universalDomain Q F A ⟶ F where
  app B := evaluationAt Q F A B
  naturality _ _ f := evaluationAt_naturality Q F A f

/-- A whole parameter simplex is evaluated at the actual QA identity, before scalar extension. -/
def resolvedParameterFamily (Q : AlgebraReplacementFunctor k) (F : Prestack k)
    (j : Families (affineParameterPrestack Q F)) :
    Families (universalDomain Q F j.obj.1) :=
  family (universalDomain Q F j.obj.1) (Q.functor.obj j.obj.1) j.obj.2
    (ULift.up (Functor.HomObj.ofNatTrans (𝟙 (Q.functor.obj j.obj.1))), j.val)

/-- The original augmentation is the actual affine zero simplex, with its native degeneracies. -/
def affineOrigin (Q : AlgebraReplacementFunctor k) (A : SAlg k) :
    (Δ[0] : SSet.{u + 1}) ⟶ (affineMapping k Q A).obj A :=
  SSet.const (ULift.up (Functor.HomObj.ofNatTrans (Q.augmentation.app A)))

/-- The graph retains every original affine mapping parameter. -/
def originGraph (Q : AlgebraReplacementFunctor k) (F : Prestack k) (A : SAlg k) :
    affineParameters Q F A ⟶ ((affineMapping k Q A).obj A) ⊗ affineParameters Q F A where
  app _ := ↾fun a => (ULift.up (Functor.HomObj.ofNatTrans (Q.augmentation.app A)), a)
  naturality _ _ _ := rfl

/-- Its geometric point is the same native evaluation at the actual augmentation. -/
def parameterPoint (Q : AlgebraReplacementFunctor k) (F : Prestack k) (A : SAlg k) :
    affineParameters Q F A ⟶ F.obj A :=
  originGraph Q F A ≫ evaluationAt Q F A A

/-- Native augmentation evaluation is natural in the actual coefficient algebra maps. -/
def affineParameterPoint (Q : AlgebraReplacementFunctor k) (F : Prestack k) :
    affineParameterPrestack Q F ⟶ F where
  app A := parameterPoint Q F A
  naturality A B f := by
    ext n a
    change ((a.app n (𝟙 n)).app B)
        (ULift.up (Functor.HomObj.ofNatTrans (Q.functor.map f ≫ Q.augmentation.app B))) =
      (F.map f).app n (((a.app n (𝟙 n)).app A)
        (ULift.up (Functor.HomObj.ofNatTrans (Q.augmentation.app A))))
    rw [Q.augmentation.naturality f]
    exact congrArg (fun t => t (ULift.up
      (Functor.HomObj.ofNatTrans (Q.augmentation.app A)))) ((a.app n (𝟙 n)).naturality f)

/-- A strict splitting supplies its actual augmented algebra mapping simplex. -/
def strictSplittingParameter (Q : AlgebraReplacementFunctor k) (F : Prestack k)
    {A : SAlg k} (E : SquareZeroExtension A) :
    strictSplittings E ⊗ affineParameters Q F A ⟶
      ((affineMapping k Q A).obj E.algebra) ⊗ affineParameters Q F A where
  app _ := ↾fun p =>
    (ULift.up (Functor.HomObj.ofNatTrans (Q.augmentation.app A ≫ p.1.down.map)), p.2)
  naturality _ _ _ := rfl

/-- The full splitting action is evaluation on these actual splitting simplices. -/
def strictUniversalAction (Q : AlgebraReplacementFunctor k) (F : Prestack k)
    {A : SAlg k} (E : SquareZeroExtension A) :
    strictSplittings E ⊗ affineParameters Q F A ⟶ F.obj E.algebra :=
  strictSplittingParameter Q F E ≫ evaluationAt Q F A E.algebra

/-- In every simplicial degree and at every native mapping parameter, the action is F(delta). -/
theorem strictUniversalAction_value (Q : AlgebraReplacementFunctor k) (F : Prestack k)
    {A : SAlg k} (E : SquareZeroExtension A) (n : SimplexCategoryᵒᵖ)
    (s : AlgebraSplitting E) (a : (affineParameters Q F A).obj n) :
    (strictUniversalAction Q F E).app n (ULift.up s, a) =
      (F.map s.map).app n ((parameterPoint Q F A).app n a) := by
  have h := congrArg (fun t => t (ULift.up
    (Functor.HomObj.ofNatTrans (Q.augmentation.app A))))
    ((a.app n (𝟙 n)).naturality s.map)
  exact h

/-- The universal geometric derivative is the actual lift fibre over the whole affine parameter. -/
def geometricDerivations (Q : AlgebraReplacementFunctor k) (F : Prestack k)
    {A : SAlg k} (E : SquareZeroExtension A) (P : KanPathModel (F.obj A)) :
    SSet.{u + 1} :=
  homotopyPullback (F.map E.projection) (parameterPoint Q F A) P

/-- The source is the actual affine lift fibre, retaining the entire parameter and its gauge paths. -/
def algebraDerivations (Q : AlgebraReplacementFunctor k) (F : Prestack k)
    {A : SAlg k} (E : SquareZeroExtension A)
    (P : KanPathModel (((affineMapping k Q A).obj A) ⊗ affineParameters Q F A)) :
    SSet.{u + 1} :=
  homotopyPullback ((affineMapping k Q A).map E.projection ⊗ₘ 𝟙 _)
    (originGraph Q F A) P

/-- The actual universal derivation map is the native map of the same evaluation pullback square. -/
def universalDerivationMap (Q : AlgebraReplacementFunctor k) (F : Prestack k)
    {A : SAlg k} (E : SquareZeroExtension A)
    (PA : KanPathModel (((affineMapping k Q A).obj A) ⊗ affineParameters Q F A))
    (PF : KanPathModel (F.obj A))
    (P : SourcePathMap (evaluationAt Q F A A) PA PF) :
    algebraDerivations Q F E PA ⟶ geometricDerivations Q F E PF :=
  pullback.map
    (prod.map ((affineMapping k Q A).map E.projection ⊗ₘ 𝟙 _) (originGraph Q F A))
    (prod.lift PA.p₀ PA.p₁)
    (prod.map (F.map E.projection) (parameterPoint Q F A)) (prod.lift PF.p₀ PF.p₁)
    (prod.map (evaluationAt Q F A E.algebra) (𝟙 _)) P.map
    (prod.map (evaluationAt Q F A A) (evaluationAt Q F A A))
    (by
      apply prod.hom_ext
      · simpa only [prod.map_fst, prod.map_fst_assoc, Category.assoc] using congrArg (fun t =>
          (prod.fst (X := ((affineMapping k Q A).obj E.algebra) ⊗ affineParameters Q F A)
            (Y := affineParameters Q F A)) ≫ t)
          (evaluationAt_naturality Q F A E.projection)
      · simp [parameterPoint])
    P.endpoints.symm

/-- The map preserves the literal original affine mapping parameter. -/
theorem universalDerivationMap_over (Q : AlgebraReplacementFunctor k) (F : Prestack k)
    {A : SAlg k} (E : SquareZeroExtension A)
    (PA : KanPathModel (((affineMapping k Q A).obj A) ⊗ affineParameters Q F A))
    (PF : KanPathModel (F.obj A))
    (P : SourcePathMap (evaluationAt Q F A A) PA PF) :
    universalDerivationMap Q F E PA PF P ≫
      SimplicialHomotopyLimits.second (F.map E.projection) (parameterPoint Q F A) PF =
    SimplicialHomotopyLimits.second
      ((affineMapping k Q A).map E.projection ⊗ₘ 𝟙 _) (originGraph Q F A) PA := by
  simp [universalDerivationMap, SimplicialHomotopyLimits.second, Category.assoc]

end MathlibExt.AlgebraicGeometry.DerivedUniversalAffineSplittingMaps
