/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CanonicalStableMatrixNaturality

/-!
# Lifted Chevalley–Eilenberg maps of stable matrix algebras

Let `k` be a commutative ring and `A` a unital `k`-algebra. Lift the Chevalley–Eilenberg
complex of the stable finite-support matrix Lie algebra to a chosen joint carrier universe.
Each finite matrix inclusion induces a lifted exterior-power chain map into this complex.

For an algebra homomorphism `f : A → B`, applying `f` to matrix entries gives a stable Lie
homomorphism and a lifted CE map. Its degree component is the lift of the corresponding
exterior-power map. These maps commute with finite-stage inclusions, with independent entry-
algebra carrier universes.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w z

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- The lifted CE complex of a stable matrix Lie algebra.

For `A`, lift the canonical complex of its stable finite-support matrix Lie algebra to the
carrier universe joining the ground, entry-algebra, and chosen lift universes. -/
abbrev canonicalStableMatrixCEComplexAtHeight :=
  canonicalComplexULift.{u,v,max u v z} k (canonicalStableMatrixAlgebra k A)

/-- The lifted finite-matrix inclusion into stable CE chains.

For every size `m`, the finite matrix Lie inclusion induces a lifted chain map to the stable
matrix CE complex. -/
def canonicalStableMatrixCEInclusionAtHeight (m : ℕ) :
    matrixComplexAtHeight.{u,v,z} k A m ⟶ canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A :=
  nativeLiftedComplexMapAtHeight.{u,v,v,z} k (Matrix (Fin m) (Fin m) A)
    (canonicalStableMatrixLieInclusion k A m)

variable {B : Type w} [Ring B] [Algebra k B]

/-- The lifted stable matrix CE map of an entry-algebra homomorphism.

For `f : A →ₐ[k] B`, entrywise application induces a chain map between lifted stable matrix
complexes in their common carrier universe. -/
def canonicalStableMatrixCoefficientCEMapAtHeight (f : A →ₐ[k] B) :
    canonicalStableMatrixCEComplexAtHeight.{u,v,max u v w z} k A ⟶
      canonicalStableMatrixCEComplexAtHeight.{u,w,max u v w z} k B :=
  nativeLiftedComplexMapAtHeight.{u,v,w,z} k (canonicalStableMatrixAlgebra k A)
    (canonicalStableMatrixCoefficientLieHom k A f)

/-- The exterior component of a lifted stable matrix coefficient map.

The degree-`n` component sends `up(a)` to `up(⋀ⁿ(f_stable)(a))`. -/
theorem canonicalStableMatrixCoefficientCEMapAtHeight_f_up (f : A →ₐ[k] B) (n : ℕ)
    (a : ⋀[k]^n (canonicalStableMatrixAlgebra k A)) :
    ((canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f).f n).hom (ULift.up a) =
      ULift.up (exteriorPower.map n (canonicalStableMatrixCoefficientLieHom k A f).toLinearMap a) :=
  nativeLiftedComplexMapAtHeight_f_up.{u,v,w,z} k (canonicalStableMatrixAlgebra k A)
    (canonicalStableMatrixCoefficientLieHom k A f) n a

/-- Naturality of lifted stable CE maps with finite matrix inclusions.

Including finite matrices and then applying the stable coefficient map equals applying the
finite entrywise coefficient map and then including into the target stable complex. -/
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
