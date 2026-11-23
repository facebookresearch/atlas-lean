/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.Homology.FundamentalGroup
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# The concrete one-chain quotient computes simplicial H1

The quotient one-chain groupoid construction uses the explicit additive
group of one-cycles modulo two-boundaries.  This file identifies that group
with Mathlib's abstract homology object in degree one.

The comparison is built only from public short-complex APIs: an explicit
three-term short complex, `HomologicalComplex.homologyIsoSc'`,
`ShortComplex.homologyMapIso`, and `ShortComplex.abHomologyIso`.  No private
chain-complex implementation or opaque colimit choice is unfolded.

This packet makes no connected Hurewicz Iso, connector naturality,
finite-BGL, kernel, plus-construction, or `Q = +` claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe u

namespace SSet

/-- The displayed degree-one short complex
`C₂(X;ℤ) ⟶ C₁(X;ℤ) ⟶ C₀(X;ℤ)`. -/
noncomputable abbrev integralDegreeOneShortComplex (X : SSet.{u}) :
    ShortComplex AddCommGrpCat.{u} :=
  let K := X.chainComplex
    (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u})
  ShortComplex.mk (K.d 2 1) (K.d 1 0) (K.d_comp_d 2 1 0)

/-- The short complex selected internally by the homological-complex API is
canonically isomorphic to the explicitly displayed degree-one short
complex. -/
noncomputable def integralDegreeOneShortComplexIso (X : SSet.{u}) :
    let K := X.chainComplex
      (AlgebraicTopology.singularIntegralCoefficients :
        AddCommGrpCat.{u})
    K.sc' 2 1 0 ≅ integralDegreeOneShortComplex X := by
  let K := X.chainComplex
    (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u})
  let S := K.sc' 2 1 0
  let T := integralDegreeOneShortComplex X
  exact ShortComplex.isoMk
    (eqToIso (HomologicalComplex.shortComplexFunctor'_obj_X₁
      AddCommGrpCat (ComplexShape.down ℕ) 2 1 0 K))
    (eqToIso (HomologicalComplex.shortComplexFunctor'_obj_X₂
      AddCommGrpCat (ComplexShape.down ℕ) 2 1 0 K))
    (eqToIso (HomologicalComplex.shortComplexFunctor'_obj_X₃
      AddCommGrpCat (ComplexShape.down ℕ) 2 1 0 K))

/-- On the displayed short complex, Mathlib's boundary-to-cycles map is the
explicit restriction of `d₂₁` used by the quotient one-chain construction. -/
theorem integralDegreeOneShortComplex_abToCycles
    (X : SSet.{u}) :
    (integralDegreeOneShortComplex X).abToCycles =
      oneBoundariesToCycles X := by
  ext a
  rfl

/-- The explicit boundary subgroups in the two concrete presentations of
degree-one homology agree. -/
theorem integralDegreeOneShortComplex_boundary_range
    (X : SSet.{u}) :
    AddMonoidHom.range (integralDegreeOneShortComplex X).abToCycles =
      AddMonoidHom.range (oneBoundariesToCycles X) :=
  congrArg AddMonoidHom.range
    (integralDegreeOneShortComplex_abToCycles X)

/-- Mathlib's abstract integral simplicial homology in degree one is
canonically isomorphic to the explicit cycles-modulo-boundaries quotient
used by the quotient one-chain groupoid. -/
noncomputable def homologyOneConcreteQuotientIso (X : SSet.{u}) :
    X.homology
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u}) 1 ≅
      AddCommGrpCat.of (integralHomologyOneQuotient X) := by
  let K := X.chainComplex
    (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u})
  let S := integralDegreeOneShortComplex X
  let e := K.homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (integralDegreeOneShortComplexIso X) ≪≫
      S.abHomologyIso
  rw [integralDegreeOneShortComplex_abToCycles] at e
  exact e

/-- The concrete forward map from the simplicial fundamental group, now
transported to Mathlib's abstract integral homology object in degree one. -/
noncomputable def fundamentalGroupHomologyOneHom
    (X : SSet.{u}) (x : X _⦋0⦌) :
    End (SSet.FundamentalGroupoid.mk x) →*
      Multiplicative
        (↑(X.homology
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u}) 1) : Type u) :=
  let e := (homologyOneConcreteQuotientIso X).symm.addCommGroupIsoToAddEquiv
  e.toMultiplicative.toMonoidHom.comp
    (fundamentalGroupConcreteHomologyOneHom X x)

/-- The abstract degree-one homology map factors through the abelianization
of the based simplicial fundamental group. -/
noncomputable def fundamentalGroupAbelianizationHomologyOneHom
    (X : SSet.{u}) (x : X _⦋0⦌) :
    Abelianization (End (SSet.FundamentalGroupoid.mk x)) →*
      Multiplicative
        (↑(X.homology
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u}) 1) : Type u) :=
  Abelianization.lift (fundamentalGroupHomologyOneHom X x)

@[simp]
theorem fundamentalGroupAbelianizationHomologyOneHom_of
    (X : SSet.{u}) (x : X _⦋0⦌)
    (q : End (SSet.FundamentalGroupoid.mk x)) :
    fundamentalGroupAbelianizationHomologyOneHom X x
        (Abelianization.of q) =
      fundamentalGroupHomologyOneHom X x q :=
  rfl

end SSet

end
