/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate

/-!
# Normalized chain complex inclusion and coefficient functoriality of `P∞`

This file provides the fixed-coefficient inclusion from the normalized chain
complex to the unnormalized chain complex, and the commutation of the
coefficient-indexed chain functor with `P∞`.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicTopology.DoldKan
open scoped Simplicial

universe w v u

namespace SSet

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- The natural inclusion from the normalized chain complex to the unnormalized
chain complex, for fixed coefficients `R : C`.

Its components are the pointwise split monomorphisms
`SSet.fromNormalizedChainComplex`. This bundles the pointwise inclusion into a
natural transformation
`SSet.normalizedChainComplexFunctorObj R ⟶ (SSet.chainComplexFunctor C).obj R`
using Mathlib's existing normalized chain-map API. -/
noncomputable def fromNormalizedChainComplexNatTrans (R : C) :
    SSet.normalizedChainComplexFunctorObj (C := C) R ⟶ (SSet.chainComplexFunctor C).obj R where
  app X := X.fromNormalizedChainComplex R
  naturality X Y f := by
    dsimp only [normalizedChainComplexFunctorObj]
    rw [← cancel_epi (X.toNormalizedChainComplex R)]
    simp only [toNormalizedChainComplex_normalizedChainComplexMap_assoc,
      toNormalizedChainComplex_fromNormalizedChainComplex_assoc,
      toNormalizedChainComplex_fromNormalizedChainComplex]
    exact chainComplexMap_PInfty f R

/-- The component at a simplicial set `X` of the natural transformation
`(SSet.chainComplexFunctor C).map f` for a coefficient morphism `f : R ⟶ S`
commutes with the two instances of `P∞`.

For each `X : SSet`, let `F := Limits.sigmaConst ⋙ SimplicialObject.whiskering`
be the coefficient-to-simplicial-object functor, so that
`(SSet.chainComplexFunctor C).map f` at `X` is
`alternatingFaceMapComplex C`-applied to `(F.map f).app X`.
Then naturality of `AlgebraicTopology.DoldKan.natTransPInfty C` at the simplicial
map `(F.map f).app X` gives
`map f ≫ P∞ = P∞ ≫ map f`, where the left `P∞` is on `X.chainComplex S` and the
right `P∞` is on `X.chainComplex R`. -/
@[reassoc]
theorem chainComplexFunctor_map_app_PInfty {R S : C} (f : R ⟶ S) (X : SSet.{w}) :
    ((SSet.chainComplexFunctor C).map f).app X ≫
      (AlgebraicTopology.DoldKan.PInfty : X.chainComplex S ⟶ X.chainComplex S) =
    (AlgebraicTopology.DoldKan.PInfty : X.chainComplex R ⟶ X.chainComplex R) ≫
      ((SSet.chainComplexFunctor C).map f).app X := by
  let F : C ⥤ SSet.{w} ⥤ SimplicialObject C :=
    Limits.sigmaConst ⋙ SimplicialObject.whiskering _ _
  have h : ((SSet.chainComplexFunctor C).map f).app X =
    (AlgebraicTopology.alternatingFaceMapComplex C).map ((F.map f).app X) := rfl
  rw [h]
  exact (AlgebraicTopology.DoldKan.natTransPInfty C).naturality ((F.map f).app X)

private noncomputable def chainComplexFunctorPInfty :
    SSet.chainComplexFunctor C ⟶ SSet.chainComplexFunctor C :=
  (Functor.postcompose₂.map (natTransPInfty C)).app
    (Limits.sigmaConst ⋙ SimplicialObject.whiskering _ _)
private lemma chainComplexFunctorPInfty_app_eq (R : C) :
    (chainComplexFunctorPInfty C).app R =
      toNormalizedChainComplexNatTrans (C := C) R ≫
        fromNormalizedChainComplexNatTrans (C := C) R := by
  apply NatTrans.ext; funext X
  exact (toNormalizedChainComplex_fromNormalizedChainComplex (X := X) (R := R)).symm
private lemma from_to_eq_id (R : C) :
    fromNormalizedChainComplexNatTrans (C := C) R ≫
      toNormalizedChainComplexNatTrans (C := C) R = 𝟙 _ := by
  apply NatTrans.ext; funext X
  exact fromNormalizedChainComplex_toNormalizedChainComplex (X := X) (R := R)
private lemma PInfty_comp_to (R : C) :
    (chainComplexFunctorPInfty C).app R ≫
      toNormalizedChainComplexNatTrans (C := C) R =
      toNormalizedChainComplexNatTrans (C := C) R := by
  calc _ = (toNormalizedChainComplexNatTrans (C := C) R ≫
          fromNormalizedChainComplexNatTrans (C := C) R) ≫ _ := by
        rw [chainComplexFunctorPInfty_app_eq]
    _ = _ ≫ (fromNormalizedChainComplexNatTrans (C := C) R ≫
          toNormalizedChainComplexNatTrans (C := C) R) := by rw [Category.assoc]
    _ = _ ≫ 𝟙 _ := by rw [from_to_eq_id]
    _ = _ := by rw [Category.comp_id]

/-- The normalized chain complex as a functor from coefficient objects to
simplicial-set-indexed chain complexes. -/
noncomputable def normalizedChainComplexFunctor : C ⥤ SSet.{w} ⥤ ChainComplex C ℕ where
  obj R := normalizedChainComplexFunctorObj (C := C) R
  map {R S} f := fromNormalizedChainComplexNatTrans (C := C) R ≫
      (chainComplexFunctor C).map f ≫ toNormalizedChainComplexNatTrans (C := C) S
  map_id R := by
    have h := (chainComplexFunctor C).map_id R
    calc _ = fromNormalizedChainComplexNatTrans (C := C) R ≫
          𝟙 _ ≫ toNormalizedChainComplexNatTrans (C := C) R := by rw [h]
      _ = _ := by rw [Category.id_comp]
      _ = _ := from_to_eq_id _ _
  map_comp {R S T} f g := by
    have hfg := (chainComplexFunctor C).map_comp f g
    have hNat : (chainComplexFunctorPInfty C).app S ≫ (chainComplexFunctor C).map g =
        (chainComplexFunctor C).map g ≫ (chainComplexFunctorPInfty C).app T :=
      ((chainComplexFunctorPInfty C).naturality g).symm
    have hRHS : (fromNormalizedChainComplexNatTrans (C := C) R ≫
          (chainComplexFunctor C).map f ≫ toNormalizedChainComplexNatTrans (C := C) S) ≫
        (fromNormalizedChainComplexNatTrans (C := C) S ≫
          (chainComplexFunctor C).map g ≫ toNormalizedChainComplexNatTrans (C := C) T) =
        fromNormalizedChainComplexNatTrans (C := C) R ≫
          (chainComplexFunctor C).map (f ≫ g) ≫
          toNormalizedChainComplexNatTrans (C := C) T := by
      calc _ = fromNormalizedChainComplexNatTrans (C := C) R ≫
            (chainComplexFunctor C).map f ≫ toNormalizedChainComplexNatTrans (C := C) S ≫
            fromNormalizedChainComplexNatTrans (C := C) S ≫
            (chainComplexFunctor C).map g ≫
            toNormalizedChainComplexNatTrans (C := C) T := by simp only [Category.assoc]
        _ = fromNormalizedChainComplexNatTrans (C := C) R ≫
            (chainComplexFunctor C).map f ≫
            (toNormalizedChainComplexNatTrans (C := C) S ≫
              fromNormalizedChainComplexNatTrans (C := C) S) ≫
            (chainComplexFunctor C).map g ≫
            toNormalizedChainComplexNatTrans (C := C) T := by simp only [Category.assoc]
        _ = fromNormalizedChainComplexNatTrans (C := C) R ≫
            (chainComplexFunctor C).map f ≫ (chainComplexFunctorPInfty C).app S ≫
            (chainComplexFunctor C).map g ≫
            toNormalizedChainComplexNatTrans (C := C) T := by
            rw [← chainComplexFunctorPInfty_app_eq]
        _ = fromNormalizedChainComplexNatTrans (C := C) R ≫
            (chainComplexFunctor C).map f ≫
            ((chainComplexFunctorPInfty C).app S ≫ (chainComplexFunctor C).map g) ≫
            toNormalizedChainComplexNatTrans (C := C) T := by simp only [Category.assoc]
        _ = fromNormalizedChainComplexNatTrans (C := C) R ≫
            (chainComplexFunctor C).map f ≫
            ((chainComplexFunctor C).map g ≫ (chainComplexFunctorPInfty C).app T) ≫
            toNormalizedChainComplexNatTrans (C := C) T := by rw [hNat]
        _ = fromNormalizedChainComplexNatTrans (C := C) R ≫
            (chainComplexFunctor C).map f ≫ (chainComplexFunctor C).map g ≫
            (chainComplexFunctorPInfty C).app T ≫
            toNormalizedChainComplexNatTrans (C := C) T := by simp only [Category.assoc]
        _ = fromNormalizedChainComplexNatTrans (C := C) R ≫
            (chainComplexFunctor C).map f ≫ (chainComplexFunctor C).map g ≫
            ((chainComplexFunctorPInfty C).app T ≫
              toNormalizedChainComplexNatTrans (C := C) T) := rfl
        _ = fromNormalizedChainComplexNatTrans (C := C) R ≫
            (chainComplexFunctor C).map f ≫ (chainComplexFunctor C).map g ≫
            toNormalizedChainComplexNatTrans (C := C) T := by rw [PInfty_comp_to]
        _ = fromNormalizedChainComplexNatTrans (C := C) R ≫
            ((chainComplexFunctor C).map f ≫ (chainComplexFunctor C).map g) ≫
            toNormalizedChainComplexNatTrans (C := C) T := by simp only [Category.assoc]
        _ = fromNormalizedChainComplexNatTrans (C := C) R ≫
            (chainComplexFunctor C).map (f ≫ g) ≫
            toNormalizedChainComplexNatTrans (C := C) T := by rw [← hfg]
    exact hRHS.symm

/-- Object part is the fixed-coefficient functor. -/
@[simp]
theorem normalizedChainComplexFunctor_obj (R : C) :
    (normalizedChainComplexFunctor (C := C)).obj R =
      normalizedChainComplexFunctorObj (C := C) R := rfl

/-- Map part at `X` is inclusion ≫ unnormalized map ≫ projection. -/
@[simp]
theorem normalizedChainComplexFunctor_map_app {R S : C} (f : R ⟶ S) (X : SSet.{w}) :
    ((normalizedChainComplexFunctor (C := C)).map f).app X =
      X.fromNormalizedChainComplex R ≫
        ((chainComplexFunctor C).map f).app X ≫ X.toNormalizedChainComplex S := rfl

/-- The normalized inclusion absorbs `P∞`: for every `X` and `R`,
`X.fromNormalizedChainComplex R ≫ P∞ = X.fromNormalizedChainComplex R`. -/
@[reassoc (attr := simp)]
theorem fromNormalizedChainComplex_comp_PInfty (X : SSet.{w}) (R : C) :
    X.fromNormalizedChainComplex (C := C) R ≫
      (AlgebraicTopology.DoldKan.PInfty : X.chainComplex R ⟶ X.chainComplex R) =
      X.fromNormalizedChainComplex R := by
  have hP : (PInfty : X.chainComplex R ⟶ X.chainComplex R) =
      X.toNormalizedChainComplex R ≫ X.fromNormalizedChainComplex R :=
    (toNormalizedChainComplex_fromNormalizedChainComplex (X := X) (R := R)).symm
  calc X.fromNormalizedChainComplex R ≫
        (PInfty : X.chainComplex R ⟶ X.chainComplex R)
      = X.fromNormalizedChainComplex R ≫
        (X.toNormalizedChainComplex R ≫ X.fromNormalizedChainComplex R) :=
        congrArg (X.fromNormalizedChainComplex R ≫ ·) hP
    _ = (X.fromNormalizedChainComplex R ≫ X.toNormalizedChainComplex R) ≫
        X.fromNormalizedChainComplex R :=
        (Category.assoc _ _ _).symm
    _ = 𝟙 _ ≫ X.fromNormalizedChainComplex R := by
        rw [fromNormalizedChainComplex_toNormalizedChainComplex]
    _ = X.fromNormalizedChainComplex R := by rw [Category.id_comp]

/-- For `f : R ⟶ S` and `X`, the component at `X` of
`normalizedChainComplexFunctor.map f`, followed by `X.fromNormalizedChainComplex S`,
equals `X.fromNormalizedChainComplex R` followed by the component at `X` of
`chainComplexFunctor.map f`. -/
theorem fromNormalizedChainComplex_coefficient_naturality {R S : C} (f : R ⟶ S)
    (X : SSet.{w}) :
    ((normalizedChainComplexFunctor (C := C)).map f).app X ≫
        X.fromNormalizedChainComplex (C := C) S =
      X.fromNormalizedChainComplex (C := C) R ≫
        ((chainComplexFunctor C).map f).app X := by
  rw [normalizedChainComplexFunctor_map_app]
  change (X.fromNormalizedChainComplex R ≫ ((chainComplexFunctor C).map f).app X ≫
      X.toNormalizedChainComplex S) ≫ X.fromNormalizedChainComplex S =
    X.fromNormalizedChainComplex R ≫ ((chainComplexFunctor C).map f).app X
  rw [Category.assoc, Category.assoc,
    toNormalizedChainComplex_fromNormalizedChainComplex]
  change X.fromNormalizedChainComplex R ≫
      (((chainComplexFunctor C).map f).app X ≫
        (AlgebraicTopology.DoldKan.PInfty :
          X.chainComplex S ⟶ X.chainComplex S)) =
    X.fromNormalizedChainComplex R ≫ ((chainComplexFunctor C).map f).app X
  rw [chainComplexFunctor_map_app_PInfty]
  change X.fromNormalizedChainComplex R ≫
      (AlgebraicTopology.DoldKan.PInfty : X.chainComplex R ⟶ X.chainComplex R) ≫
      ((chainComplexFunctor C).map f).app X =
    X.fromNormalizedChainComplex R ≫ ((chainComplexFunctor C).map f).app X
  exact fromNormalizedChainComplex_comp_PInfty_assoc C X R _

section DegenerateKilling

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- Normalized projection kills degenerate simplices (element form). -/
theorem ιChainComplex_comp_toNormalized_eq_zero
    (X : SSet.{w}) (R : C) {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.degenerate n) :
    X.ιChainComplex (R := R) x ≫ (X.toNormalizedChainComplex R).f n = 0 := by
  rw [SSet.ιChainComplex_toNormalizedChainComplex_f]
  exact SSet.ιNormalizedChainComplex_eq_zero X x hx

/-- Normalized projection kills explicit degeneracies. -/
theorem ιChainComplex_σ_comp_toNormalized_eq_zero
    (X : SSet.{w}) (R : C) {n : ℕ} (y : X _⦋n⦌) (i : Fin (n + 1)) :
    X.ιChainComplex (R := R) (X.σ i y) ≫
      (X.toNormalizedChainComplex R).f (n + 1) = 0 :=
  ιChainComplex_comp_toNormalized_eq_zero X R _ (X.σ_mem_degenerate i y)

/-- Finite sums of degenerate generators vanish under normalized projection:
the recombination form for "k degenerate summands vanish". -/
theorem sum_ιChainComplex_degenerate_comp_toNormalized_eq_zero
    (X : SSet.{w}) (R : C) {n : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → X _⦋n⦌) (hx : ∀ i, x i ∈ X.degenerate n) :
    (∑ i, X.ιChainComplex (R := R) (x i)) ≫
      (X.toNormalizedChainComplex R).f n = 0 := by
  rw [Preadditive.sum_comp]
  exact Finset.sum_eq_zero fun i _ =>
    ιChainComplex_comp_toNormalized_eq_zero X R _ (hx i)

end DegenerateKilling

end SSet
