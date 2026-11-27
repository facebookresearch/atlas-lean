/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralLinearFrameSchemes
public import MathlibExt.AlgebraicGeometry.ExpansionParameterModels
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Actual GL2/SL2 matrix schemes and rank-one group maps

GL2 reuses the actual determinant-localized frame scheme and its frame
dictionary. The matrix dictionary is normalized on every test scheme,
including nonreduced coefficient algebras. SL2 is Spec of the actual
matrix-coordinate algebra modulo determinant minus1.

Weyl, diagonal and unipotent maps are actual scheme maps obtained from
their specified universal matrices. The rank-one normalizer parameters
therefore retain the SL2 lifts even when a coroot has a finite kernel.
Sources: Donagi--Gaitsgory arXiv:math/0005132v3, Sections6--8;
de Cataldo--Hausel--Migliorini arXiv:1004.1420v2, Section1.2.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.RankTwoMatrixGroupModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open GeneralLinearFrameSchemes ExpansionParameterModels
open scoped Matrix

variable [F : FrameTheory 2]

class GL2MatrixTheory where
  points : ∀ U : Over (Spec (.of ℂ)),
    (U ⟶ frameScheme 2) ≃ Matrix.GeneralLinearGroup (Fin 2) Γ(U.left, ⊤)
  coordinates : ∀ (U : Over (Spec (.of ℂ))) (f : U ⟶ frameScheme 2) (i j : Fin 2),
    f.left.appTop.hom (coordinate 2 i j) = points U f i j
  identity : ∀ U, points U (toUnit U ≫ η[frameScheme 2]) = 1
  multiply : ∀ (U : Over (Spec (.of ℂ))) (f g : U ⟶ frameScheme 2),
    points U (CartesianMonoidalCategory.lift f g ≫ μ[frameScheme 2]) = points U f * points U g
  naturality : ∀ {U U' : Over (Spec (.of ℂ))} (h : U' ⟶ U) (f : U ⟶ frameScheme 2),
    points U' (h ≫ f) = Matrix.GeneralLinearGroup.map h.left.appTop.hom (points U f)

def determinantOneIdeal : Ideal (MatrixPolynomial 2) := Ideal.span {genericDeterminant 2 - 1}

abbrev SL2Ring := MatrixPolynomial 2 ⧸ determinantOneIdeal

def sl2Scheme : Over (Spec (.of ℂ)) := Over.mk (Spec.algebraMap ℂ SL2Ring)

def sl2Coordinate (i j : Fin 2) : Γ(sl2Scheme.left, ⊤) :=
  (Scheme.ΓSpecIso (.of SL2Ring)).inv.hom
    (algebraMap (MatrixPolynomial 2) SL2Ring (MvPolynomial.X (i, j)))

variable [M : GL2MatrixTheory]

class SL2MatrixTheory where
  [group : GrpObj sl2Scheme]
  points : ∀ U : Over (Spec (.of ℂ)),
    (U ⟶ sl2Scheme) ≃ Matrix.SpecialLinearGroup (Fin 2) Γ(U.left, ⊤)
  coordinates : ∀ (U : Over (Spec (.of ℂ))) (f : U ⟶ sl2Scheme) (i j : Fin 2),
    f.left.appTop.hom (sl2Coordinate i j) = points U f i j
  identity : ∀ U, points U (toUnit U ≫ η[sl2Scheme]) = 1
  multiply : ∀ (U : Over (Spec (.of ℂ))) (f g : U ⟶ sl2Scheme),
    points U (CartesianMonoidalCategory.lift f g ≫ μ[sl2Scheme]) = points U f * points U g
  naturality : ∀ {U U' : Over (Spec (.of ℂ))} (h : U' ⟶ U) (f : U ⟶ sl2Scheme),
    points U' (h ≫ f) = Matrix.SpecialLinearGroup.map h.left.appTop.hom (points U f)
  inclusion : sl2Scheme ⟶ frameScheme 2
  [inclusion_hom : IsMonHom inclusion]
  inclusion_points : ∀ (U : Over (Spec (.of ℂ))) (f : U ⟶ sl2Scheme),
    M.points U (f ≫ inclusion) = (points U f).toGL

attribute [instance_reducible, instance] SL2MatrixTheory.group
attribute [instance] SL2MatrixTheory.inclusion_hom

def minusGL (R : Type) [CommRing R] : Matrix.GeneralLinearGroup (Fin 2) R where
  val := -1
  inv := -1
  val_inv := by simp
  inv_val := by simp

def weylMatrix (R : Type) [CommRing R] : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

def diagonalMatrix {R : Type} [CommRing R] (u : Rˣ) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![↑u, 0; 0, ↑u⁻¹], by simp [Matrix.det_fin_two]⟩

def upperMatrix {R : Type} [CommRing R] (x : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩

def lowerMatrix {R : Type} [CommRing R] (x : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![1, 0; x, 1], by simp [Matrix.det_fin_two]⟩

variable [S : SL2MatrixTheory]

def minusPoint : 𝟙_ (Over (Spec (.of ℂ))) ⟶ frameScheme 2 :=
  (M.points (𝟙_ (Over (Spec (.of ℂ))))).symm (minusGL Γ(Spec (.of ℂ), ⊤))

def weylPoint : 𝟙_ (Over (Spec (.of ℂ))) ⟶ sl2Scheme :=
  (S.points (𝟙_ (Over (Spec (.of ℂ))))).symm (weylMatrix Γ(Spec (.of ℂ), ⊤))

def diagonal (Gm : TorusTheory ℂ 1) : torusScheme ℂ 1 ⟶ sl2Scheme :=
  (S.points (torusScheme ℂ 1)).symm
    (diagonalMatrix (Gm.units (torusScheme ℂ 1) (𝟙 (torusScheme ℂ 1)) 0))

def upper : affineLine ℂ ⟶ sl2Scheme :=
  (S.points (affineLine ℂ)).symm (upperMatrix (affineCoordinate ℂ))

def lower : affineLine ℂ ⟶ sl2Scheme :=
  (S.points (affineLine ℂ)).symm (lowerMatrix (affineCoordinate ℂ))

end MathlibExt.AlgebraicGeometry.RankTwoMatrixGroupModels
