/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.CoordinateOrthogonality

/-!
# Tensor cells at a fixed total cochain degree

Let R be a commutative ring and P,Q integer cochain complexes with independent module carrier
universes. In total degree n, use the cells P^i⊗Q^{n−i}. Their inclusions are transported
along i+(n−i)=n, and their projections are the canonical tensor-cell projections.

A cell projection retracts its own inclusion and kills an inclusion with any different first
degree. No support or finite-generation condition is needed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex

universe u v w x y

namespace CochainComplex.ModuleTensor

variable (R : Type u) [CommRing R]
  (P : CochainComplex (ModuleCat.{v} R) ℤ) (Q : CochainComplex (ModuleCat.{w} R) ℤ)

/-- For a commutative ring R, integer cochain complexes P,Q in independent module universes, and
n,i ∈ ℤ, define P^i⊗Q^{n−i} → (P⊗Q)^n by the tensor-cell inclusion followed by the total-term
transport along i+(n−i)=n. -/
def degreeComponentInclusionAt (n i : ℤ) :
    ModuleCat.tensorObjAt R (P.X i) (Q.X (n - i)) ⟶ (complexAt R P Q).X n :=
  componentInclusionAt R P Q i (n - i) ≫
    ((complexAt R P Q).XIsoOfEq (show i + (n - i) = n by omega)).hom

/-- Let R be a commutative ring, P,Q integer R-module cochain complexes, and n,i ∈ ℤ. The
projection (P⊗Q)^n → P^i⊗Q^{n−i} is tensorCellProjection at the supported pair (i,n−i). The
two module universes may be independent. -/
abbrev degreeComponentProjectionAt (n i : ℤ) :
    (complexAt R P Q).X n ⟶ ModuleCat.tensorObjAt R (P.X i) (Q.X (n - i)) :=
  tensorCellProjection R P Q i (n - i) n

/-- For a commutative ring R, integer module cochain complexes P,Q, and n,i ∈ ℤ,
degreeComponentInclusionAt(n,i) equals the canonical coproduct inclusion indexed by i,n−i into
total degree n, using the equality i+(n−i)=n. -/
theorem degreeComponentInclusionAt_eq_native (n i : ℤ) :
    degreeComponentInclusionAt R P Q n i =
      HomologicalComplex.ιMapBifunctor P Q (ModuleCat.tensorBifunctorAt R) (.up ℤ)
        i (n - i) n (show i + (n - i) = n by omega) :=
  nativeComponentInclusion_cast R P Q i (n - i) (i + (n - i)) n rfl (by omega)

/-- Let R be a commutative ring and P,Q integer R-module cochain complexes. For n,i ∈ ℤ, inclusion
of P^i⊗Q^{n−i} into (P⊗Q)^n followed by its degree-i projection is the identity of
P^i⊗Q^{n−i}. -/
theorem degreeComponentInclusionAt_projectionAt (n i : ℤ) :
    degreeComponentInclusionAt R P Q n i ≫ degreeComponentProjectionAt R P Q n i =
      𝟙 (ModuleCat.tensorObjAt R (P.X i) (Q.X (n - i))) := by
  rw [degreeComponentInclusionAt_eq_native]
  exact tensorCellProjection_ι R P Q i (n - i) n (by omega)

/-- For a commutative ring R, integer module cochain complexes P,Q, and n,p,i ∈ ℤ with p≠i, the
inclusion of P^p⊗Q^{n−p} into total degree n followed by the projection onto P^i⊗Q^{n−i} is
zero. -/
theorem degreeComponentInclusionAt_other_projectionAt (n p i : ℤ) (hpi : p ≠ i) :
    degreeComponentInclusionAt R P Q n p ≫ degreeComponentProjectionAt R P Q n i = 0 := by
  rw [degreeComponentInclusionAt_eq_native]
  exact tensorCellProjection_ι_eq_zero R P Q i (n - i) n p (n - p) (by omega) (Or.inl hpi)

end CochainComplex.ModuleTensor
