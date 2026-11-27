/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticGroupTorsorSites
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Actual algebraic group representations and cocharacters on all algebra tests

Group points are the native group scheme evaluated on Spec of each
actual E-algebra, including nonreduced and zero algebras. A representation
or cocharacter is a natural group homomorphism on this entire diagram.
The linear target is the native invertible-matrix group; G_m is the
native unit group. Weight splitting is fixed on every algebra and unit
by the original E basis matrix and its scalar extension.

No unrelated representation or cocharacter carrier is selected.
Sources: Fargues--Scholze, arXiv:2102.13459v4, Sections VI.1--VI.2;
SGA 3, representations of diagonalizable groups.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AlgebraicGroupPointRepresentations

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicGeometry

variable (E : Type) [CommRing E]

def testSchemes : (CommAlgCat.{0} E)ᵒᵖ ⥤ Over (Spec (.of E)) where
  obj R := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap E R.unop)))
  map {R S} f := Over.homMk (Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap E S.unop)) =
        Spec.map (CommRingCat.ofHom (algebraMap E R.unop))
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact f.unop.hom.commutes a)
  map_id R := by
    apply Over.OverMorphism.ext
    change Spec.map (𝟙 (CommRingCat.of R.unop)) = 𝟙 _
    exact Spec.map_id _
  map_comp f g := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (f ≫ g).unop.hom.toRingHom) =
      Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom g.unop.hom.toRingHom)
    rw [← Spec.map_comp]
    congr 1

variable (G : Over (Spec (.of E))) [GrpObj G]

def groups : CommAlgCat.{0} E ⥤ GrpCat := (testSchemes E).rightOp ⋙ yonedaGrpObj G

def linearGroups (n : ℕ) : CommAlgCat.{0} E ⥤ GrpCat where
  obj R := GrpCat.of (GL (Fin n) R)
  map f := GrpCat.ofHom (Matrix.GeneralLinearGroup.map f.hom.toRingHom)
  map_id R := by
    exact congrArg GrpCat.ofHom (Matrix.GeneralLinearGroup.map_id)
  map_comp f g := by
    exact congrArg GrpCat.ofHom (Matrix.GeneralLinearGroup.map_comp _ _)

def unitGroups : CommAlgCat.{0} E ⥤ GrpCat where
  obj R := GrpCat.of Rˣ
  map f := GrpCat.ofHom (Units.map f.hom.toMonoidHom)
  map_id _R := rfl
  map_comp _f _g := rfl

abbrev Representation (n : ℕ) := groups E G ⟶ linearGroups E n
abbrev Cocharacter := unitGroups E ⟶ groups E G

variable (n : ℕ) (ρ : Representation E G n) (μ : Cocharacter E G)

def actionMatrix (R : CommAlgCat.{0} E) (g : (groups E G).obj R) :
    Matrix (Fin n) (Fin n) R :=
  (show GL (Fin n) R from (ρ.app R).hom g).val

/-- This is the actual character decomposition, normalized on every E-algebra and unit. -/
structure WeightSplitting where
  basis : GL (Fin n) E
  weight : Fin n → ℤ
  dominant : Antitone weight
  matrix_normalized : ∀ (R : CommAlgCat.{0} E) (u : Rˣ),
    actionMatrix E G n ρ R ((μ.app R).hom u) =
      (Matrix.GeneralLinearGroup.map (algebraMap E R) basis : Matrix (Fin n) (Fin n) R) *
        Matrix.diagonal (fun i ↦ ((u ^ weight i : Rˣ) : R)) *
          (Matrix.GeneralLinearGroup.map (algebraMap E R) basis⁻¹ : Matrix (Fin n) (Fin n) R)

end MathlibExt.AlgebraicGeometry.AlgebraicGroupPointRepresentations
