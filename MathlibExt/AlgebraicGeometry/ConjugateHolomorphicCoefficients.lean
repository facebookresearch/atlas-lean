/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves
public import MathlibExt.AlgebraicGeometry.DifferentialOperatorSheaves

/-!
# The original conjugate holomorphic coefficient and differential rings

The underlying ring remains the original holomorphic-function ring and
its scalar map is conjugated. Its function realization conjugates the
original section values, so it is the antiholomorphic coefficient sheaf
on the same real manifold. Its differential ring is the same native
finite-order operator/sheafification construction on those coefficients.

Source: DK arXiv:1311.2374v2, Definition 5.2.1 and the preceding conjugate
complex manifold convention. Native coefficient/ring APIs are Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ConjugateHolomorphicCoefficients

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open scoped Manifold ContDiff

/-- Conjugate only the actual complex scalar map of the original ring. -/
def conjugateObject (A : CommAlgCat.{0} ℂ) : CommAlgCat.{0} ℂ :=
  { carrier := A
    commRing := inferInstance
    algebra := ((algebraMap ℂ A).comp (starRingEnd ℂ)).toAlgebra }

def conjugateMap {A B : CommAlgCat.{0} ℂ} (f : A ⟶ B) :
    conjugateObject A ⟶ conjugateObject B := by
  let g : A →+* B := f.hom.toRingHom
  have hg : ∀ c : ℂ, g (algebraMap ℂ A (star c)) = algebraMap ℂ B (star c) :=
    fun c => f.hom.commutes (star c)
  letI : Algebra ℂ A := (conjugateObject A).algebra
  letI : Algebra ℂ B := (conjugateObject B).algebra
  exact CommAlgCat.ofHom { g with commutes' := hg }

def conjugateScalars : CommAlgCat.{0} ℂ ⥤ CommAlgCat.{0} ℂ where
  obj A := conjugateObject A
  map f := conjugateMap f
  map_id A := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    rfl
  map_comp f g := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    rfl

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def conjugateCoefficientPresheaf : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} ℂ :=
  HolomorphicCoefficientSheaves.coefficientPresheaf E M ⋙ conjugateScalars

/-- The actual conjugate function value in the source real manifold. -/
def conjugateValue {U : Opens M} (f : (conjugateCoefficientPresheaf E M).obj (op U))
    (x : U) : ℂ := star (f.val x)

def conjugateOperatorPresheaf : (Opens M)ᵒᵖ ⥤ RingCat.{0} :=
  DifferentialOperatorSheaves.operatorPresheaf ℂ M (conjugateCoefficientPresheaf E M)

def conjugateDifferentialRing [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}] :
    TopCat.Sheaf RingCat.{0} (TopCat.of M) :=
  DifferentialOperatorSheaves.differentialRing ℂ M (conjugateCoefficientPresheaf E M)

end MathlibExt.AlgebraicGeometry.ConjugateHolomorphicCoefficients
