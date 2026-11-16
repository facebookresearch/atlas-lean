/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeWittLoopTests
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.Algebra.Group.ULift

/-!
# Witt Grassmannian and convolution as actual quotient sheaves

The Grassmannian is the fpqc sheafification of LG/L+G. The twofold
convolution quotient is the sheafification of (LG times LG)/(L+G times L+G),
with action (g,k).(h,j) = (g h, h^{-1} k j). Its multiplication map is
induced by actual group multiplication. Neither quotient carries a freely
chosen multiplication, geometric space or monoidal sheaf category.

The coefficient test rings are the literal W(R) tensor W(k) B and its
pi-localization from RelativeWittLoopTests; the local-field application
uses B = O_E. Every action and multiplication retains those same tests.

Reference: Zhu, arXiv:1407.8519v3, Sections1.1 and1.4. The quotient and
sheafification are completed native category constructions. Ind-perfect
geometry, equivariant perverse coefficients and Satake are separate inputs
and conclusions, not consequences claimed here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.RelativeWittLoopCorrespondences

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open RelativeWittLoopTests

variable (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k]
  (B : Type) [CommRing B] [Algebra (WittVector p k) B] (pi : B)
  (G : Over (Spec (.of B))) [GrpObj G]

abbrev AffinePresheaf := PerfectAlgebra p k ⥤ Type 1

/-- Only lift the actual geometric point sets to the site's sheaf universe. -/
def loopSets : AffinePresheaf p k :=
  loops p k B pi G ⋙ forget GrpCat ⋙ uliftFunctor.{1, 0}

/-- The actual positive-loop point sets, in the same universe. -/
def positiveSets : AffinePresheaf p k :=
  positiveLoops p k B G ⋙ forget GrpCat ⋙ uliftFunctor.{1, 0}

instance loopSetsGroup (R : PerfectAlgebra p k) :
    Group ((loopSets p k B pi G).obj R) :=
  inferInstanceAs (Group (ULift.{1} ((loops p k B pi G).obj R)))

instance positiveSetsGroup (R : PerfectAlgebra p k) :
    Group ((positiveSets p k B G).obj R) :=
  inferInstanceAs (Group (ULift.{1} ((positiveLoops p k B G).obj R)))

/-- The prescribed inclusion of the actual positive-loop point sets. -/
def inclusion : positiveSets p k B G ⟶ loopSets p k B pi G :=
  Functor.whiskerRight (positiveToLoop p k B pi G)
    (forget GrpCat ⋙ uliftFunctor.{1, 0})

/-- Product of actual presheaves, with the actual pointwise maps. -/
def pairs (A B : AffinePresheaf p k) : AffinePresheaf p k where
  obj R := A.obj R × B.obj R
  map f := TypeCat.ofHom fun x ↦ (A.map f x.1, B.map f x.2)
  map_id R := by ext x <;> simp
  map_comp f g := by ext x <;> simp

/-- The actual right action used to define the Grassmannian. -/
def rightAction : pairs p k (loopSets p k B pi G) (positiveSets p k B G) ⟶ loopSets p k B pi G where
  app R := TypeCat.ofHom fun x ↦ x.1 * (inclusion p k B pi G).app R x.2
  naturality {R S} f := by
    ext x
    symm
    change ULift.up ((loops p k B pi G).map f
      (x.1.down * (positiveToLoop p k B pi G).app R x.2.down)) = _
    rw [map_mul]
    exact congrArg ULift.up (congrArg (fun y ↦ (loops p k B pi G).map f x.1.down * y)
      (congrArg (fun h ↦ h x.2.down) ((positiveToLoop p k B pi G).naturality f).symm))

/-- Forget the positive-loop factor in the actual action domain. -/
def rightProjection : pairs p k (loopSets p k B pi G) (positiveSets p k B G) ⟶
    loopSets p k B pi G where
  app R := TypeCat.ofHom Prod.fst

/-- The literal right-action quotient, prior to fpqc sheafification. -/
def grassmannianPresheaf : AffinePresheaf p k :=
  coequalizer (rightAction p k B pi G) (rightProjection p k B pi G)

/-- The fixed quotient map on the actual loop points. -/
def quotient : loopSets p k B pi G ⟶ grassmannianPresheaf p k B pi G :=
  coequalizer.π (rightAction p k B pi G) (rightProjection p k B pi G)

/-- Every actual positive-loop translate represents the same quotient point. -/
theorem quotient_translate (R : PerfectAlgebra p k) (g : (loopSets p k B pi G).obj R)
    (h : (positiveSets p k B G).obj R) :
    (quotient p k B pi G).app R (g * (inclusion p k B pi G).app R h) =
      (quotient p k B pi G).app R g := by
  exact congrArg (fun t ↦ t.app R (g, h))
    (coequalizer.condition (rightAction p k B pi G) (rightProjection p k B pi G))

/-- The actual convolution action domain. -/
def convolutionActionDomain : AffinePresheaf p k :=
  pairs p k (pairs p k (loopSets p k B pi G) (loopSets p k B pi G))
    (pairs p k (positiveSets p k B G) (positiveSets p k B G))

/-- The middle and right positive-loop changes of trivialization. -/
def convolutionAction : convolutionActionDomain p k B pi G ⟶
    pairs p k (loopSets p k B pi G) (loopSets p k B pi G) where
  app R := TypeCat.ofHom fun x ↦
    (x.1.1 * (inclusion p k B pi G).app R x.2.1,
      ((inclusion p k B pi G).app R x.2.1)⁻¹ * x.1.2 * (inclusion p k B pi G).app R x.2.2)
  naturality {R S} f := by
    ext x
    symm
    have h₁ := congrArg (fun h ↦ h x.2.1.down)
      ((positiveToLoop p k B pi G).naturality f).symm
    have h₂ := congrArg (fun h ↦ h x.2.2.down)
      ((positiveToLoop p k B pi G).naturality f).symm
    change (loops p k B pi G).map f ((positiveToLoop p k B pi G).app R x.2.1.down) =
      (positiveToLoop p k B pi G).app S ((positiveLoops p k B G).map f x.2.1.down) at h₁
    change (loops p k B pi G).map f ((positiveToLoop p k B pi G).app R x.2.2.down) =
      (positiveToLoop p k B pi G).app S ((positiveLoops p k B G).map f x.2.2.down) at h₂
    change (ULift.up ((loops p k B pi G).map f
        (x.1.1.down * (positiveToLoop p k B pi G).app R x.2.1.down)),
      ULift.up ((loops p k B pi G).map f
        (((positiveToLoop p k B pi G).app R x.2.1.down)⁻¹ * x.1.2.down *
          (positiveToLoop p k B pi G).app R x.2.2.down))) =
      (ULift.up ((loops p k B pi G).map f x.1.1.down *
        (positiveToLoop p k B pi G).app S ((positiveLoops p k B G).map f x.2.1.down)),
      ULift.up (((positiveToLoop p k B pi G).app S
        ((positiveLoops p k B G).map f x.2.1.down))⁻¹ *
          (loops p k B pi G).map f x.1.2.down * (positiveToLoop p k B pi G).app S
            ((positiveLoops p k B G).map f x.2.2.down)))
    simp only [map_mul, map_inv, h₁, h₂]

/-- Forget the actual changes of trivialization. -/
def convolutionProjection : convolutionActionDomain p k B pi G ⟶
    pairs p k (loopSets p k B pi G) (loopSets p k B pi G) where
  app R := TypeCat.ofHom Prod.fst

/-- The actual twofold twisted quotient before sheafification. -/
def convolutionPresheaf : AffinePresheaf p k :=
  coequalizer (convolutionAction p k B pi G) (convolutionProjection p k B pi G)

/-- Actual multiplication of loop points, followed by the fixed quotient. -/
def productToGrassmannian : pairs p k (loopSets p k B pi G) (loopSets p k B pi G) ⟶
    grassmannianPresheaf p k B pi G where
  app R := TypeCat.ofHom fun x ↦ (quotient p k B pi G).app R (x.1 * x.2)
  naturality {R S} f := by
    ext x
    have h := congrArg (fun t ↦ t (x.1 * x.2)) ((quotient p k B pi G).naturality f)
    change (quotient p k B pi G).app S
      ((loopSets p k B pi G).map f x.1 * (loopSets p k B pi G).map f x.2) =
          (grassmannianPresheaf p k B pi G).map f ((quotient p k B pi G).app R (x.1 * x.2))
    have hm : (loopSets p k B pi G).map f (x.1 * x.2) =
        (loopSets p k B pi G).map f x.1 * (loopSets p k B pi G).map f x.2 := by
      apply ULift.ext
      exact map_mul ((loops p k B pi G).map f).hom _ _
    rw [← hm]
    exact h

/-- Multiplication is invariant under both actual changes of trivialization. -/
theorem multiplication_invariant :
    convolutionAction p k B pi G ≫ productToGrassmannian p k B pi G =
      convolutionProjection p k B pi G ≫ productToGrassmannian p k B pi G := by
  ext R x
  change (quotient p k B pi G).app R
    ((x.1.1 * (inclusion p k B pi G).app R x.2.1) *
      (((inclusion p k B pi G).app R x.2.1)⁻¹ * x.1.2 *
        (inclusion p k B pi G).app R x.2.2)) =
          (quotient p k B pi G).app R (x.1.1 * x.1.2)
  have h : (x.1.1 * (inclusion p k B pi G).app R x.2.1) *
      (((inclusion p k B pi G).app R x.2.1)⁻¹ * x.1.2 *
        (inclusion p k B pi G).app R x.2.2) =
          (x.1.1 * x.1.2) * (inclusion p k B pi G).app R x.2.2 := by
    simp only [_root_.mul_assoc, mul_inv_cancel_left]
  rw [h]
  exact quotient_translate p k B pi G R (x.1.1 * x.1.2) x.2.2

/-- The convolution morphism is the actual coequalizer-descended product. -/
def multiplication : convolutionPresheaf p k B pi G ⟶ grassmannianPresheaf p k B pi G :=
  coequalizer.desc (productToGrassmannian p k B pi G) (multiplication_invariant p k B pi G)

/-- The actual fpqc Grassmannian sheaf, independent of a representing model. -/
def grassmannian : Sheaf (fpqcTopology p k) (Type 1) :=
  (presheafToSheaf (fpqcTopology p k) (Type 1)).obj
    ((opOpEquivalence (PerfectAlgebra p k)).functor ⋙ grassmannianPresheaf p k B pi G)

/-- The actual fpqc convolution sheaf. -/
def convolution : Sheaf (fpqcTopology p k) (Type 1) :=
  (presheafToSheaf (fpqcTopology p k) (Type 1)).obj
    ((opOpEquivalence (PerfectAlgebra p k)).functor ⋙ convolutionPresheaf p k B pi G)

/-- Its fixed multiplication map, induced by the same sheafification functor. -/
def convolutionMap : convolution p k B pi G ⟶ grassmannian p k B pi G :=
  (presheafToSheaf (fpqcTopology p k) (Type 1)).map
    (Functor.whiskerLeft (opOpEquivalence (PerfectAlgebra p k)).functor
      (multiplication p k B pi G))

end MathlibExt.AlgebraicGeometry.RelativeWittLoopCorrespondences
