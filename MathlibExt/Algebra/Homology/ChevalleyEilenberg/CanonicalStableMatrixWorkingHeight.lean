/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CanonicalStableMatrixNaturality

/-!
# Universe lifts of stable matrix Chevalley–Eilenberg maps

Universe lifting places stable matrix Chevalley–Eilenberg complexes and their finite-stage
inclusions in a common module category. Algebra homomorphisms induce chain maps whose
components are the lifted exterior-power maps.

The coefficient carrier universes may be independent, while the ground ring is fixed.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w z

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- Prolongation of CE of the canonical stable matrix Lie algebra. -/
abbrev canonicalStableMatrixCEComplexAtHeight :=
  canonicalComplexULift.{u,v,max u v z} k (canonicalStableMatrixAlgebra k A)

/-- Every finite matrix Lie inclusion induces its prolonged CE map. -/
def canonicalStableMatrixCEInclusionAtHeight (m : ℕ) :
    matrixComplexAtHeight.{u,v,z} k A m ⟶ canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A :=
  nativeLiftedComplexMapAtHeight.{u,v,v,z} k (Matrix (Fin m) (Fin m) A)
    (canonicalStableMatrixLieInclusion k A m)

variable {B : Type w} [Ring B] [Algebra k B]

/-- Coefficient universes give canonical CE maps at their common height. -/
def canonicalStableMatrixCoefficientCEMapAtHeight (f : A →ₐ[k] B) :
    canonicalStableMatrixCEComplexAtHeight.{u,v,max u v w z} k A ⟶
      canonicalStableMatrixCEComplexAtHeight.{u,w,max u v w z} k B :=
  nativeLiftedComplexMapAtHeight.{u,v,w,z} k (canonicalStableMatrixAlgebra k A)
    (canonicalStableMatrixCoefficientLieHom k A f)

/-- The prolonged coefficient map retains the exterior map on every degree. -/
theorem canonicalStableMatrixCoefficientCEMapAtHeight_f_up (f : A →ₐ[k] B) (n : ℕ)
    (a : ⋀[k]^n (canonicalStableMatrixAlgebra k A)) :
    ((canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f).f n).hom (ULift.up a) =
      ULift.up (exteriorPower.map n (canonicalStableMatrixCoefficientLieHom k A f).toLinearMap a) :=
  nativeLiftedComplexMapAtHeight_f_up.{u,v,w,z} k (canonicalStableMatrixAlgebra k A)
    (canonicalStableMatrixCoefficientLieHom k A f) n a

/-- The finite coefficient square holds without identifying the coefficient universes. -/
@[reassoc]
theorem canonicalStableMatrixCoefficientCEMapAtHeight_inclusion (f : A →ₐ[k] B) (m : ℕ) :
    canonicalStableMatrixCEInclusionAtHeight.{u,v,max u v w z} k A m ≫
        canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f =
      matrixCoefficientMapAtHeight.{u,v,w,z} k A f m ≫
        canonicalStableMatrixCEInclusionAtHeight.{u,w,max u v w z} k B m := by
  let ia := canonicalStableMatrixLieInclusion k A m
  let ib := canonicalStableMatrixLieInclusion k B m
  let c := canonicalStableMatrixCoefficientLieHom k A f
  let t := Matrix.coefficientLieHom k A f m
  have h₁ := nativeLiftedComplexMapAtHeight_comp.{u,v,v,w,max u v w z} k
    (Matrix (Fin m) (Fin m) A) ia c
  have h₂ := nativeLiftedComplexMapAtHeight_comp.{u,v,w,w,max u v w z} k
    (Matrix (Fin m) (Fin m) A) t ib
  have hLie : c.comp ia = ib.comp t := canonicalStableMatrixCoefficientLieHom_inclusion k A f m
  have hMap := congrArg (nativeLiftedComplexMapAtHeight.{u,v,w,max u v w z} k
    (Matrix (Fin m) (Fin m) A)) hLie
  exact h₁.trans (hMap.trans h₂.symm)

end ChevalleyEilenberg
