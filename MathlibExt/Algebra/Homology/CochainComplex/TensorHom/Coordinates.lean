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

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.Basic

/-!
# Inclusions and projections of cochain tensor cells

Let R be a commutative ring and P,Q integer cochain complexes with independent carrier
universes. The term (P⊗Q)^n is the coproduct of P^p⊗Q^q over p+q=n. Each pair has a canonical
inclusion at its sum degree.

For arbitrary displayed n,j,b, the tensor-cell projection selects the (j,b) summand and kills
every other pair. If j+b=n, its composite with that cell inclusion is the identity. No support
bounds are required.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace CochainComplex.ModuleTensor

variable (R : Type u) [CommRing R]

attribute [local instance] instHasMapBifunctorModuleCatIntTensorBifunctorAtUp

/-- Let R be a commutative ring, P,Q integer R-module cochain complexes in universes v,w, and p,q
∈ ℤ. The canonical coproduct inclusion P^p⊗_R Q^q → (P⊗Q)^{p+q} defines componentInclusionAt.
The tensor term has carrier universe max(v,w), and no boundedness assumption is used. -/
def componentInclusionAt (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (Q : CochainComplex (ModuleCat.{w} R) ℤ) (p q : ℤ) :
    ModuleCat.tensorObjAt R (P.X p) (Q.X q) ⟶ (complexAt R P Q).X (p + q) :=
  HomologicalComplex.ιMapBifunctor P Q (ModuleCat.tensorBifunctorAt R) (.up ℤ)
    p q (p + q) rfl

/-- For integer R-module cochain complexes J,U in independent carrier universes and j,b,n ∈ ℤ,
define (J⊗U)^n → J^j⊗_R U^b by coproduct descent. On a summand indexed by (j′,b′) with j′+b′=n
it is the identity if j′=j and b′=b, and zero otherwise. In particular, no equality j+b=n is
required to define the projection. -/
def tensorCellProjection (J : CochainComplex (ModuleCat.{v} R) ℤ)
    (U : CochainComplex (ModuleCat.{w} R) ℤ)
    (j b n : ℤ) :
    (complexAt R J U).X n ⟶ ModuleCat.tensorObjAt R (J.X j) (U.X b) :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := J) (K₂ := U) (F := ModuleCat.tensorBifunctorAt R) (c := .up ℤ)
      (fun j' b' _ => by
        by_cases hj : j' = j
        · subst j'
          by_cases hb : b' = b
          · subst b'
            exact 𝟙 _
          · exact 0
        · exact 0)

/-- Let R be a commutative ring, J,U integer cochain complexes with independent module carrier
universes, and j+b=n. The canonical inclusion J^j⊗U^b → (J⊗U)^n followed by the projection
onto (j,b) is the identity of J^j⊗U^b. -/
theorem tensorCellProjection_ι (J : CochainComplex (ModuleCat.{v} R) ℤ)
    (U : CochainComplex (ModuleCat.{w} R) ℤ)
    (j b n : ℤ) (hjb : j + b = n) :
    HomologicalComplex.ιMapBifunctor J U (ModuleCat.tensorBifunctorAt R) (.up ℤ)
        j b n hjb ≫ tensorCellProjection R J U j b n = 𝟙 _ := by
  unfold tensorCellProjection
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp
  rfl

/-- For integer R-module cochain complexes J,U over a commutative ring R, let j′+b′=n and suppose
j′≠j or b′≠b. The inclusion of J^{j′}⊗U^{b′} into (J⊗U)^n followed by the projection onto
(j,b) is zero. The displayed target cell need not itself have sum n. -/
theorem tensorCellProjection_ι_eq_zero (J : CochainComplex (ModuleCat.{v} R) ℤ)
    (U : CochainComplex (ModuleCat.{w} R) ℤ)
    (j b n j' b' : ℤ) (hjb' : j' + b' = n)
    (h : j' ≠ j ∨ b' ≠ b) :
    HomologicalComplex.ιMapBifunctor J U (ModuleCat.tensorBifunctorAt R) (.up ℤ)
        j' b' n hjb' ≫ tensorCellProjection R J U j b n = 0 := by
  unfold tensorCellProjection
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  by_cases hj : j' = j
  · subst j'
    have hb : b' ≠ b := h.resolve_left (not_not_intro rfl)
    simp [hb]
  · simp [hj]

theorem tensorCellProjection_mk (J : CochainComplex (ModuleCat.{v} R) ℤ)
    (U : CochainComplex (ModuleCat.{w} R) ℤ)
    (j b n : ℤ) (hjb : j + b = n) (x : J.X j) (u : U.X b) :
    (tensorCellProjection R J U j b n).hom (mkAt R J U j b n hjb x u) =
      x ⊗ₜ[R] u := by
  have h := congrArg (fun f : ModuleCat.tensorObjAt R (J.X j) (U.X b) ⟶
      ModuleCat.tensorObjAt R (J.X j) (U.X b) => f.hom (x ⊗ₜ[R] u))
    (tensorCellProjection_ι R J U j b n hjb)
  exact h

theorem tensorCellProjection_mk_eq_zero (J : CochainComplex (ModuleCat.{v} R) ℤ)
    (U : CochainComplex (ModuleCat.{w} R) ℤ)
    (j b n j' b' : ℤ) (hjb' : j' + b' = n)
    (h : j' ≠ j ∨ b' ≠ b) (x : J.X j') (u : U.X b') :
    (tensorCellProjection R J U j b n).hom (mkAt R J U j' b' n hjb' x u) = 0 := by
  have hi := tensorCellProjection_ι_eq_zero R J U j b n j' b' hjb' h
  have hv := congrArg (fun f : ModuleCat.tensorObjAt R (J.X j') (U.X b') ⟶
      ModuleCat.tensorObjAt R (J.X j) (U.X b) => f.hom (x ⊗ₜ[R] u)) hi
  exact hv

end CochainComplex.ModuleTensor
