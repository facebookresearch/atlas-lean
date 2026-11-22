/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftPiEquivalence

@[expose] public section

/-!
# Exact original source-map naturality of Kan homotopy universe lift

Every original full pointed-simplex map and same actual source map
commute with the canonical coefficient lift. The original quotient
representative induction proves the whole based homotopy-group square
in every dimension and independent coefficient universe.
-/

noncomputable section

universe u v

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.KanComplex

/-- The same original full represented-simplex source map commutes with the actual coefficient lift. -/
theorem uliftStandardHomEquiv_postcomp {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) (p : (Δ[n] : SSet.{u}) ⟶ X) :
    SSet.uliftStandardHomEquiv.{u,v} Y ⦋n⦌ (p ≫ f) =
      SSet.uliftStandardHomEquiv.{u,v} X ⦋n⦌ p ≫ SSet.uliftFunctor.map f := by
  apply SSet.yonedaEquiv.injective
  have hL := Equiv.apply_symm_apply (SSet.yonedaEquiv (X := SSet.uliftFunctor.{v,u}.obj Y))
    (SSet.uliftObjEquiv Y _ (SSet.yonedaEquiv (p ≫ f)))
  have hR := Equiv.apply_symm_apply (SSet.yonedaEquiv (X := SSet.uliftFunctor.{v,u}.obj X))
    (SSet.uliftObjEquiv X _ (SSet.yonedaEquiv p))
  exact hL.trans
    ((congrArg (SSet.uliftObjEquiv Y _) (SSet.yonedaEquiv_comp p f)).trans
      ((congrArg (fun x => (SSet.uliftFunctor.map f).app _ x) hR).symm.trans
        (SSet.yonedaEquiv_comp (SSet.uliftStandardHomEquiv X ⦋n⦌ p) (SSet.uliftFunctor.map f)).symm))

/-- The same full original pointed-simplex map retains the exact coefficient-lift source square. -/
theorem uliftPointedSimplex_map {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) (x : X _⦋0⦌) (p : X.PtSimplex n x) :
    SSet.uliftPointedSimplexEquiv.{u,v} Y n (f.app _ x) (PtSimplex.map f rfl p) =
      PtSimplex.map (SSet.uliftFunctor.map f) rfl (SSet.uliftPointedSimplexEquiv.{u,v} X n x p) := by
  apply RelativeMorphism.ext
  exact uliftStandardHomEquiv_postcomp f n (RelativeMorphism.map p)

/-- Every actual original quotient-map square commutes with the entire Kan homotopy-group universe equivalence. -/
theorem uliftPiEquiv_naturality {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) (n : ℕ) (x : X _⦋0⦌) (p : π n X x) :
    uliftPiEquiv.{u,v} Y n (f.app _ x) (π.map f rfl n p) =
      π.map (SSet.uliftFunctor.map f) rfl n (uliftPiEquiv.{u,v} X n x p) := by
  induction p using π.rec with
  | mk p => exact congrArg π.mk (uliftPointedSimplex_map f n x p)

end SSet.KanComplex
