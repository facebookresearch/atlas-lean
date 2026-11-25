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
# Cochain tensor cells in independent carrier universes

`tensorCellProjection` is defined at arbitrary displayed degrees with
independent carrier universes. It uses the coproduct descriptor and its
characteristic maps, without support or boundedness assumptions.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace CochainComplex.ModuleTensor

variable (R : Type u) [CommRing R]

attribute [local instance] instHasMapBifunctorModuleCatIntTensorBifunctorAtUp

/-- The native inclusion of the original two factor degrees in their actual sum degree. -/
def componentInclusionAt (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (Q : CochainComplex (ModuleCat.{w} R) ℤ) (p q : ℤ) :
    ModuleCat.tensorObjAt R (P.X p) (Q.X q) ⟶ (complexAt R P Q).X (p + q) :=
  HomologicalComplex.ιMapBifunctor P Q (ModuleCat.tensorBifunctorAt R) (.up ℤ)
    p q (p + q) rfl

/-- The native total desc onto an original tensor cell at an arbitrary displayed degree. -/
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

/-- Projection of the actual supported tensor coprojection is its original identity. -/
theorem tensorCellProjection_ι (J : CochainComplex (ModuleCat.{v} R) ℤ)
    (U : CochainComplex (ModuleCat.{w} R) ℤ)
    (j b n : ℤ) (hjb : j + b = n) :
    HomologicalComplex.ιMapBifunctor J U (ModuleCat.tensorBifunctorAt R) (.up ℤ)
        j b n hjb ≫ tensorCellProjection R J U j b n = 𝟙 _ := by
  unfold tensorCellProjection
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp
  rfl

/-- Every different original coefficient cell is killed by that same actual projection. -/
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
