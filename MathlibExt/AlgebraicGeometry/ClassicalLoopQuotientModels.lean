/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ClassicalLoopCoefficientTests
public import MathlibExt.AlgebraicGeometry.GeneralStackGeometry
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.Algebra.Group.ULift

/-!
# The actual formal-loop Grassmannian and twisted-product quotient

The original loop group uses R[[z]][1/z] on all B-algebra tests. Its
Grassmannian and twisted product are the native fpqc sheafifications of
the original loop quotients. Multiplication is the same coequalizer-
descended group multiplication, with both positive-loop actions fixed.
For the complex geometry of classical Satake set B=C; the sheaf
coefficient ring remains a separate input.

This adapts the completed native quotient constructions in
RelativeWittLoopCorrespondences to the full formal-loop test diagram.
It does not replace the classical loops by Witt vectors or finite flags.
References: Mirkovic--Vilonen, arXiv:math/0401222v5, Sections2/4/5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ClassicalLoopQuotientModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open ClassicalLoopCoefficientTests

variable (B : Type) [CommRing B] (G : Over (Spec (.of B))) [GrpObj G]

/-- The actual fpqc topology pulled back along original affine Spec tests. -/
def fpqcTopology : GrothendieckTopology (CommAlgCat.{0} B)ᵒᵖ :=
  (AlgebraicGroupPointRepresentations.testSchemes B).inducedTopology
    (Scheme.fpqcTopology.over (Spec (.of B)))

abbrev AffinePresheaf := CommAlgCat.{0} B ⥤ Type 1

/-- Only lift the actual geometric point sets to the site's sheaf universe. -/
def loopSets : AffinePresheaf B :=
  loops B G ⋙ forget GrpCat ⋙ uliftFunctor.{1, 0}

/-- The actual positive-loop point sets, in the same universe. -/
def positiveSets : AffinePresheaf B :=
  positiveLoops B G ⋙ forget GrpCat ⋙ uliftFunctor.{1, 0}

instance loopSetsGroup (R : CommAlgCat.{0} B) :
    Group ((loopSets B G).obj R) :=
  inferInstanceAs (Group (ULift.{1} ((loops B G).obj R)))

instance positiveSetsGroup (R : CommAlgCat.{0} B) :
    Group ((positiveSets B G).obj R) :=
  inferInstanceAs (Group (ULift.{1} ((positiveLoops B G).obj R)))

/-- The prescribed inclusion of the actual positive-loop point sets. -/
def inclusion : positiveSets B G ⟶ loopSets B G :=
  Functor.whiskerRight (positiveToLoop B G)
    (forget GrpCat ⋙ uliftFunctor.{1, 0})

/-- Product of actual presheaves, with the actual pointwise maps. -/
def pairs (A₁ A₂ : AffinePresheaf B) : AffinePresheaf B where
  obj R := A₁.obj R × A₂.obj R
  map f := TypeCat.ofHom fun x ↦ (A₁.map f x.1, A₂.map f x.2)
  map_id R := by ext x <;> simp
  map_comp f g := by ext x <;> simp

/-- The actual right action used to define the Grassmannian. -/
def rightAction : pairs B (loopSets B G) (positiveSets B G) ⟶ loopSets B G where
  app R := TypeCat.ofHom fun x ↦ x.1 * (inclusion B G).app R x.2
  naturality {R S} f := by
    ext x
    symm
    change ULift.up ((loops B G).map f
      (x.1.down * (positiveToLoop B G).app R x.2.down)) = _
    rw [map_mul]
    exact congrArg ULift.up (congrArg (fun y ↦ (loops B G).map f x.1.down * y)
      (congrArg (fun h ↦ h x.2.down) ((positiveToLoop B G).naturality f).symm))

/-- Forget the positive-loop factor in the actual action domain. -/
def rightProjection : pairs B (loopSets B G) (positiveSets B G) ⟶
    loopSets B G where
  app R := TypeCat.ofHom Prod.fst

/-- The literal right-action quotient, prior to fpqc sheafification. -/
def grassmannianPresheaf : AffinePresheaf B :=
  coequalizer (rightAction B G) (rightProjection B G)

/-- The fixed quotient map on the actual loop points. -/
def quotient : loopSets B G ⟶ grassmannianPresheaf B G :=
  coequalizer.π (rightAction B G) (rightProjection B G)

/-- Every actual positive-loop translate represents the same quotient point. -/
theorem quotient_translate (R : CommAlgCat.{0} B) (g : (loopSets B G).obj R)
    (h : (positiveSets B G).obj R) :
    (quotient B G).app R (g * (inclusion B G).app R h) =
      (quotient B G).app R g := by
  exact congrArg (fun t ↦ t.app R (g, h))
    (coequalizer.condition (rightAction B G) (rightProjection B G))

/-- The actual convolution action domain. -/
def convolutionActionDomain : AffinePresheaf B :=
  pairs B (pairs B (loopSets B G) (loopSets B G))
    (pairs B (positiveSets B G) (positiveSets B G))

/-- The middle and right positive-loop changes of trivialization. -/
def convolutionAction : convolutionActionDomain B G ⟶
    pairs B (loopSets B G) (loopSets B G) where
  app R := TypeCat.ofHom fun x ↦
    (x.1.1 * (inclusion B G).app R x.2.1,
      ((inclusion B G).app R x.2.1)⁻¹ * x.1.2 * (inclusion B G).app R x.2.2)
  naturality {R S} f := by
    ext x
    symm
    have h₁ := congrArg (fun h ↦ h x.2.1.down)
      ((positiveToLoop B G).naturality f).symm
    have h₂ := congrArg (fun h ↦ h x.2.2.down)
      ((positiveToLoop B G).naturality f).symm
    change (loops B G).map f ((positiveToLoop B G).app R x.2.1.down) =
      (positiveToLoop B G).app S ((positiveLoops B G).map f x.2.1.down) at h₁
    change (loops B G).map f ((positiveToLoop B G).app R x.2.2.down) =
      (positiveToLoop B G).app S ((positiveLoops B G).map f x.2.2.down) at h₂
    change (ULift.up ((loops B G).map f
        (x.1.1.down * (positiveToLoop B G).app R x.2.1.down)),
      ULift.up ((loops B G).map f
        (((positiveToLoop B G).app R x.2.1.down)⁻¹ * x.1.2.down *
          (positiveToLoop B G).app R x.2.2.down))) =
      (ULift.up ((loops B G).map f x.1.1.down *
        (positiveToLoop B G).app S ((positiveLoops B G).map f x.2.1.down)),
      ULift.up (((positiveToLoop B G).app S
        ((positiveLoops B G).map f x.2.1.down))⁻¹ *
          (loops B G).map f x.1.2.down * (positiveToLoop B G).app S
            ((positiveLoops B G).map f x.2.2.down)))
    simp only [map_mul, map_inv, h₁, h₂]

/-- Forget the actual changes of trivialization. -/
def convolutionProjection : convolutionActionDomain B G ⟶
    pairs B (loopSets B G) (loopSets B G) where
  app R := TypeCat.ofHom Prod.fst

/-- The actual twofold twisted quotient before sheafification. -/
def convolutionPresheaf : AffinePresheaf B :=
  coequalizer (convolutionAction B G) (convolutionProjection B G)

/-- Actual multiplication of loop points, followed by the fixed quotient. -/
def productToGrassmannian : pairs B (loopSets B G) (loopSets B G) ⟶
    grassmannianPresheaf B G where
  app R := TypeCat.ofHom fun x ↦ (quotient B G).app R (x.1 * x.2)
  naturality {R S} f := by
    ext x
    have h := congrArg (fun t ↦ t (x.1 * x.2)) ((quotient B G).naturality f)
    change (quotient B G).app S
      ((loopSets B G).map f x.1 * (loopSets B G).map f x.2) =
          (grassmannianPresheaf B G).map f ((quotient B G).app R (x.1 * x.2))
    have hm : (loopSets B G).map f (x.1 * x.2) =
        (loopSets B G).map f x.1 * (loopSets B G).map f x.2 := by
      apply ULift.ext
      exact map_mul ((loops B G).map f).hom _ _
    rw [← hm]
    exact h

/-- Multiplication is invariant under both actual changes of trivialization. -/
theorem multiplication_invariant :
    convolutionAction B G ≫ productToGrassmannian B G =
      convolutionProjection B G ≫ productToGrassmannian B G := by
  ext R x
  change (quotient B G).app R
    ((x.1.1 * (inclusion B G).app R x.2.1) *
      (((inclusion B G).app R x.2.1)⁻¹ * x.1.2 *
        (inclusion B G).app R x.2.2)) =
          (quotient B G).app R (x.1.1 * x.1.2)
  have h : (x.1.1 * (inclusion B G).app R x.2.1) *
      (((inclusion B G).app R x.2.1)⁻¹ * x.1.2 *
        (inclusion B G).app R x.2.2) =
          (x.1.1 * x.1.2) * (inclusion B G).app R x.2.2 := by
    simp only [_root_.mul_assoc, mul_inv_cancel_left]
  rw [h]
  exact quotient_translate B G R (x.1.1 * x.1.2) x.2.2

/-- The convolution morphism is the actual coequalizer-descended product. -/
def multiplication : convolutionPresheaf B G ⟶ grassmannianPresheaf B G :=
  coequalizer.desc (productToGrassmannian B G) (multiplication_invariant B G)

/-- The actual fpqc Grassmannian sheaf, independent of a representing model. -/
def grassmannian : Sheaf (fpqcTopology B) (Type 1) :=
  (presheafToSheaf (fpqcTopology B) (Type 1)).obj
    ((opOpEquivalence (CommAlgCat.{0} B)).functor ⋙ grassmannianPresheaf B G)

/-- The actual fpqc convolution sheaf. -/
def convolution : Sheaf (fpqcTopology B) (Type 1) :=
  (presheafToSheaf (fpqcTopology B) (Type 1)).obj
    ((opOpEquivalence (CommAlgCat.{0} B)).functor ⋙ convolutionPresheaf B G)

/-- Its fixed multiplication map, induced by the same sheafification functor. -/
def convolutionMap : convolution B G ⟶ grassmannian B G :=
  (presheafToSheaf (fpqcTopology B) (Type 1)).map
    (Functor.whiskerLeft (opOpEquivalence (CommAlgCat.{0} B)).functor
      (multiplication B G))

end MathlibExt.AlgebraicGeometry.ClassicalLoopQuotientModels
