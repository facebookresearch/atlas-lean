/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeQuiver

/-!
# Evaluation of the free simplicial category

An interpretation consists only of an original object map and actual
simplicial maps on the generating Homs. The genuine enriched functor
on all paths is the canonical computad evaluation, transported along
the explicit label adapter.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialQuiver

variable {O : Type u} (Q : Data O) (C : Type v) [EnrichedCategory SSet.{u} C]

/-- Actual images of original objects and generating simplicial arrows. -/
structure Interpretation where
  /-- The unchanged original object indexing of the chosen target images. -/
  obj : O → C
  /-- A genuine simplicial map on each original generating Hom object. -/
  map (x y : O) : Q.Hom x y ⟶ obj x ⟶[SSet.{u}] obj y

variable {Q C}

/-- The given simplicial maps supply the canonical computad assignment. -/
def Interpretation.assignment (I : Interpretation Q C) :
    SSet.SimplicialComputad.Assignment (computad Q) (C := C) where
  obj := I.obj
  atom n {x y} a := (I.map x y).app n a
  operator {n m} f {x y} a := by
    change (I.obj x ⟶[SSet.{u}] I.obj y).map f ((I.map x y).app n a) =
      SSet.SimplicialComputad.evaluate I.obj m
        (fun {x y} a => (I.map x y).app m a)
        (SSet.SimplicialComputad.single ((Q.Hom x y).map f a))
    rw [SSet.SimplicialComputad.evaluate_single]
    exact congr($((I.map x y).naturality f) a).symm

/-- The image of a whole original generating path uses actual target enriched composition. -/
def Interpretation.evalPath (I : Interpretation Q C) (n : SimplexCategoryᵒᵖ) {x y : O}
    (p : Path Q n x y) : (I.obj x ⟶[SSet.{u}] I.obj y).obj n :=
  SSet.SimplicialComputad.evaluate I.obj n (I.assignment.atom n) (toNativePath Q n p)

/-- The empty path evaluates to the actual enriched identity in its scalar degree. -/
theorem Interpretation.evalPath_nil (I : Interpretation Q C) (n : SimplexCategoryᵒᵖ) (x : O) :
    I.evalPath n (@Quiver.Path.nil O (quiverAt Q n) x) =
      (eId SSet.{u} (I.obj x)).app n PUnit.unit := rfl

/-- Appending a supplied generating arrow evaluates by the actual enriched composition. -/
theorem Interpretation.evalPath_cons (I : Interpretation Q C) (n : SimplexCategoryᵒᵖ)
    {x y z : O} (p : Path Q n x y) (a : (Q.Hom y z).obj n) :
    I.evalPath n (@Quiver.Path.cons O (quiverAt Q n) x y z p a) =
      (eComp SSet.{u} (I.obj x) (I.obj y) (I.obj z)).app n
        (I.evalPath n p, (I.map y z).app n a) := rfl

/-- Evaluation respects concatenation of arbitrary whole original paths. -/
theorem Interpretation.evalPath_comp (I : Interpretation Q C) (n : SimplexCategoryᵒᵖ)
    {x y z : O} (p : Path Q n x y) (q : Path Q n y z) :
    I.evalPath n (@Quiver.Path.comp O (quiverAt Q n) x y z p q) =
      (eComp SSet.{u} (I.obj x) (I.obj y) (I.obj z)).app n (I.evalPath n p, I.evalPath n q) := by
  change SSet.SimplicialComputad.evaluate I.obj n (I.assignment.atom n)
    (toNativePath Q n (@Quiver.Path.comp O (quiverAt Q n) x y z p q)) = _
  rw [toNativePath_comp]
  exact SSet.SimplicialComputad.evaluate_comp I.obj n (I.assignment.atom n)
    (toNativePath Q n p) (toNativePath Q n q)

/-- Every original scalar operator commutes with evaluation of the full generating path. -/
theorem Interpretation.evalPath_naturality (I : Interpretation Q C)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) {x y : O} (p : Path Q n x y) :
    I.evalPath m (mapPath Q f p) =
      (I.obj x ⟶[SSet.{u}] I.obj y).map f (I.evalPath n p) := by
  change SSet.SimplicialComputad.evaluate I.obj m (I.assignment.atom m)
    (toNativePath Q m (mapPath Q f p)) = _
  rw [toNativePath_map]
  exact (I.assignment.map_natural (computad Q) f (toNativePath Q n p)).symm

/-- The actual simplicial map evaluating all original free paths. -/
def Interpretation.evalHom (I : Interpretation Q C) (x y : O) :
    freeHom Q x y ⟶ I.obj x ⟶[SSet.{u}] I.obj y where
  app n := ↾fun p => I.evalPath n p
  naturality n m f := by
    ext p
    exact I.evalPath_naturality f p

/-- The genuine enriched free extension of the supplied interpretation. -/
def Interpretation.extend (I : Interpretation Q C) :
    letI := freeEnrichment Q
    EnrichedFunctor SSet.{u} O C := by
  letI := freeEnrichment Q
  exact EnrichedFunctor.comp SSet.{u} (toComputad Q) (I.assignment.toFunctor (computad Q))

/-- Every supplied original generator is read back by its actual given simplicial map. -/
theorem Interpretation.generator_eval (I : Interpretation Q C) (x y : O) :
    generator Q x y ≫ I.evalHom x y = I.map x y := by
  ext n a
  exact SSet.SimplicialComputad.evaluate_single I.obj n (I.assignment.atom n) a

/-- A canonical singleton-operator assignment gives its original simplicial generator maps. -/
def interpretationOfAssignment (d : SSet.SimplicialComputad.Assignment (computad Q) (C := C)) :
    Interpretation Q C where
  obj := d.obj
  map x y :=
    { app n := ↾d.atom n
      naturality := by
        intro n m f
        ext a
        exact ((d.operator f a).trans
          (SSet.SimplicialComputad.evaluate_single d.obj m (d.atom m)
            ((Q.Hom x y).map f a))).symm }

/-- Quiver interpretations are precisely assignments to the canonical singleton-operator
computad. -/
def assignmentEquiv :
    SSet.SimplicialComputad.Assignment (computad Q) (C := C) ≃ Interpretation Q C where
  toFun := interpretationOfAssignment
  invFun := Interpretation.assignment
  left_inv d := by
    apply SSet.SimplicialComputad.Assignment.ext
    · rfl
    · apply heq_of_eq
      funext n x y a
      rfl
  right_inv I := by
    cases I
    rfl

end CategoryTheory.SimplicialQuiver
