/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ConnectedComponents
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Cartesian products of connected components

The native connected-component quotient carries the original Cartesian
simplex pairs to pairs of component classes. The tensor and chosen-product
comparisons retain their actual projections, inverse vertex pairs, and
simplicial operators for arbitrary simplicial sets. The component functor
preserves finite products, including the chosen empty product.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

namespace SSet

variable {X Y : SSet.{u}}

/-- The same original pair of simplices in the actual pointwise Cartesian tensor. -/
def componentTensorSimplex (n : SimplexCategoryᵒᵖ) (x : X.obj n) (y : Y.obj n) :
    (X ⊗ Y).obj n := (x, y)

private def tensorEdge {x x' : X _⦋0⦌} {y y' : Y _⦋0⦌}
    (a : X.Edge x x') (b : Y.Edge y y') :
    (X ⊗ Y).Edge (componentTensorSimplex _ x y) (componentTensorSimplex _ x' y') :=
  Edge.mk (componentTensorSimplex _ a.edge b.edge)
    (Prod.ext a.src_eq b.src_eq) (Prod.ext a.tgt_eq b.tgt_eq)

/-- Internal use of the already-proved native cofork universal property. -/
private def piZeroDesc {A : Type u} (f : X _⦋0⦌ → A)
    (h : ∀ s : X _⦋1⦌, f (X.δ (1 : Fin 2) s) = f (X.δ (0 : Fin 2) s)) :
    π₀ X → A :=
  X.isColimitCoforkπ₀.desc (Cofork.ofπ (↾f) (by ext s; exact h s))

private theorem piZeroDesc_mk {A : Type u} (f : X _⦋0⦌ → A)
    (h : ∀ s : X _⦋1⦌, f (X.δ (1 : Fin 2) s) = f (X.δ (0 : Fin 2) s))
    (x : X _⦋0⦌) : piZeroDesc f h (π₀.mk x) = f x := by
  have hh := X.isColimitCoforkπ₀.fac
    (Cofork.ofπ (↾f) (by ext s; exact h s)) WalkingParallelPair.one
  exact congrArg (fun k => k x) hh

private def piZeroTensorRight (x : X _⦋0⦌) : π₀ Y → π₀ (X ⊗ Y) :=
  piZeroDesc (fun y => π₀.mk (componentTensorSimplex _ x y))
    (fun s => π₀.sound (tensorEdge (Edge.id x) (Edge.mk' s)))

private def piZeroTensorPair (c : π₀ X) (d : π₀ Y) : π₀ (X ⊗ Y) :=
  piZeroDesc (fun x => piZeroTensorRight (Y := Y) x) (by
    intro s
    funext d
    induction d using π₀.rec with
    | mk y =>
      simp only [piZeroTensorRight, piZeroDesc_mk]
      exact π₀.sound (tensorEdge (Edge.mk' s) (Edge.id y))) c d

private theorem piZeroTensorPair_mk (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    piZeroTensorPair (π₀.mk x) (π₀.mk y) = π₀.mk (componentTensorSimplex _ x y) := by
  unfold piZeroTensorPair
  rw [piZeroDesc_mk (X := X)]
  unfold piZeroTensorRight
  exact piZeroDesc_mk (X := Y) _ _ y

/-- The canonical component equivalence of the actual Cartesian tensor, for any ambient objects. -/
@[no_expose]
def piZeroTensorEquiv (X Y : SSet.{u}) : π₀ (X ⊗ Y) ≃ π₀ X × π₀ Y := by
  refine {
    toFun := fun c => (mapπ₀ (CartesianMonoidalCategory.fst X Y) c,
      mapπ₀ (CartesianMonoidalCategory.snd X Y) c)
    invFun := fun c => piZeroTensorPair c.1 c.2
    left_inv := ?_
    right_inv := ?_ }
  · intro c
    induction c using π₀.rec with
    | mk s =>
      rcases s with ⟨x, y⟩
      change piZeroTensorPair (π₀.mk x) (π₀.mk y) = π₀.mk (componentTensorSimplex _ x y)
      exact piZeroTensorPair_mk x y
  · intro c
    rcases c with ⟨a, b⟩
    induction a using π₀.rec with
    | mk x =>
      induction b using π₀.rec with
      | mk y =>
        change (mapπ₀ (CartesianMonoidalCategory.fst X Y)
            (piZeroTensorPair (π₀.mk x) (π₀.mk y)),
          mapπ₀ (CartesianMonoidalCategory.snd X Y)
            (piZeroTensorPair (π₀.mk x) (π₀.mk y))) = (π₀.mk x, π₀.mk y)
        rw [piZeroTensorPair_mk]
        rfl

@[simp]
theorem piZeroTensorEquiv_apply (X Y : SSet.{u}) (c : π₀ (X ⊗ Y)) :
    piZeroTensorEquiv X Y c =
      (mapπ₀ (CartesianMonoidalCategory.fst X Y) c,
        mapπ₀ (CartesianMonoidalCategory.snd X Y) c) := by rfl

/-- The inverse comparison retains the original chosen pair of vertices. -/
theorem piZeroTensorEquiv_symm_mk (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    (piZeroTensorEquiv X Y).symm (π₀.mk x, π₀.mk y) =
      π₀.mk (componentTensorSimplex _ x y) := by
  exact piZeroTensorPair_mk x y

/-- The canonical comparison between the actual tensor and the chosen categorical product. -/
def componentTensorProductIso (X Y : SSet.{u}) : X ⊗ Y ≅ X ⨯ Y :=
  (CartesianMonoidalCategory.tensorLeftIsoProd X).app Y

@[reassoc (attr := simp)]
theorem componentTensorProductIso_fst (X Y : SSet.{u}) :
    (componentTensorProductIso X Y).hom ≫ prod.fst = CartesianMonoidalCategory.fst X Y :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y) (limit.isLimit _)
        (.mk WalkingPair.left)

@[reassoc (attr := simp)]
theorem componentTensorProductIso_snd (X Y : SSet.{u}) :
    (componentTensorProductIso X Y).hom ≫ prod.snd = CartesianMonoidalCategory.snd X Y :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y) (limit.isLimit _)
        (.mk WalkingPair.right)

/-- The component equivalence for the actual chosen categorical product. -/
def piZeroProductEquiv (X Y : SSet.{u}) : π₀ (X ⨯ Y) ≃ π₀ X × π₀ Y :=
  ((π₀Functor.mapIso (componentTensorProductIso X Y).symm).toEquiv).trans
    (piZeroTensorEquiv X Y)

@[reassoc (attr := simp)]
theorem componentTensorProductIso_inv_fst (X Y : SSet.{u}) :
    (componentTensorProductIso X Y).inv ≫ CartesianMonoidalCategory.fst X Y = prod.fst := by
  rw [← componentTensorProductIso_fst, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

@[reassoc (attr := simp)]
theorem componentTensorProductIso_inv_snd (X Y : SSet.{u}) :
    (componentTensorProductIso X Y).inv ≫ CartesianMonoidalCategory.snd X Y = prod.snd := by
  rw [← componentTensorProductIso_snd, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

@[simp]
theorem piZeroProductEquiv_apply (X Y : SSet.{u}) (c : π₀ (X ⨯ Y)) :
    piZeroProductEquiv X Y c = (mapπ₀ (prod.fst : X ⨯ Y ⟶ X) c,
        mapπ₀ (prod.snd : X ⨯ Y ⟶ Y) c) := by
  change piZeroTensorEquiv X Y (mapπ₀ (componentTensorProductIso X Y).inv c) = _
  rw [piZeroTensorEquiv_apply, ← mapπ₀_comp_apply, ← mapπ₀_comp_apply,
    componentTensorProductIso_inv_fst, componentTensorProductIso_inv_snd]

/-- The original pair in the actual chosen product, not an unrelated chosen representative. -/
def componentProductSimplex (n : SimplexCategoryᵒᵖ) (x : X.obj n) (y : Y.obj n) :
    (X ⨯ Y).obj n :=
  (componentTensorProductIso X Y).hom.app n (componentTensorSimplex n x y)

@[simp]
theorem componentProductSimplex_fst (n : SimplexCategoryᵒᵖ) (x : X.obj n) (y : Y.obj n) :
    (prod.fst : X ⨯ Y ⟶ X).app n (componentProductSimplex n x y) = x := by
  exact congrArg (fun f => f.app n (componentTensorSimplex n x y))
    (componentTensorProductIso_fst X Y)

@[simp]
theorem componentProductSimplex_snd (n : SimplexCategoryᵒᵖ) (x : X.obj n) (y : Y.obj n) :
    (prod.snd : X ⨯ Y ⟶ Y).app n (componentProductSimplex n x y) = y := by
  exact congrArg (fun f => f.app n (componentTensorSimplex n x y))
    (componentTensorProductIso_snd X Y)

/-- The actual degree-zero pair gives exactly the original two component classes. -/
theorem piZeroProductEquiv_mk (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    piZeroProductEquiv X Y (π₀.mk (componentProductSimplex (op ⦋0⦌) x y)) =
      (π₀.mk x, π₀.mk y) := by
  rw [piZeroProductEquiv_apply, mapπ₀_mk, mapπ₀_mk,
    componentProductSimplex_fst, componentProductSimplex_snd]

theorem piZeroProductEquiv_symm_mk (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    (piZeroProductEquiv X Y).symm (π₀.mk x, π₀.mk y) =
      π₀.mk (componentProductSimplex (op ⦋0⦌) x y) := by
  rw [← piZeroProductEquiv_mk x y, Equiv.symm_apply_apply]

/-- Every original simplicial operator preserves the same pair of original simplices. -/
theorem componentProductSimplex_map {n m : SimplexCategoryᵒᵖ} (a : n ⟶ m)
    (x : X.obj n) (y : Y.obj n) :
    (X ⨯ Y).map a (componentProductSimplex n x y) =
      componentProductSimplex m (X.map a x) (Y.map a y) := by
  have h := (componentTensorProductIso X Y).hom.naturality a
  exact (congrArg (fun f : (X ⊗ Y).obj n ⟶ (X ⨯ Y).obj m =>
    f (componentTensorSimplex (X := X) (Y := Y) n x y)) h).symm

/-- The actual component functor preserves finite Cartesian products, including the zero-factor
unit. -/
instance piZeroFunctorPreservesFiniteProducts :
    PreservesFiniteProducts (π₀Functor : SSet.{u} ⥤ Type u) := by
  let _ : π₀Functor.{u}.OplaxMonoidal := Functor.OplaxMonoidal.ofChosenFiniteProducts _
  let _ : IsIso (Functor.OplaxMonoidal.η π₀Functor.{u}) := by
    rw [isIso_iff_bijective]
    have hs0 : Subsingleton ((𝟙_ SSet.{u}) _⦋0⦌) := by
      refine ⟨fun x y => ?_⟩
      apply (unitHomEquiv (𝟙_ SSet.{u})).symm.injective
      exact CartesianMonoidalCategory.toUnit_unique _ _
    have hs : Subsingleton (π₀ (𝟙_ SSet.{u})) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := π₀.mk_surjective a
      obtain ⟨y, rfl⟩ := π₀.mk_surjective b
      exact congrArg π₀.mk (hs0.elim x y)
    refine ⟨fun a b _ => hs.elim a b, ?_⟩
    intro z
    let c := π₀.mk (unitHomEquiv (𝟙_ SSet.{u}) (𝟙 _))
    refine ⟨c, ?_⟩
    have hh : (↾fun _ : PUnit.{u + 1} => (Functor.OplaxMonoidal.η π₀Functor).hom c) =
        (↾fun _ : PUnit.{u + 1} => z) := CartesianMonoidalCategory.toUnit_unique _ _
    exact congrArg (fun f => f PUnit.unit) hh
  let _ : ∀ A B : SSet.{u}, IsIso (Functor.OplaxMonoidal.δ π₀Functor A B) := by
    intro A B
    rw [Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory, isIso_iff_bijective]
    change Function.Bijective (fun c : π₀ (A ⊗ B) =>
      (mapπ₀ (CartesianMonoidalCategory.fst A B) c,
        mapπ₀ (CartesianMonoidalCategory.snd A B) c))
    exact (piZeroTensorEquiv A B).bijective
  let _ : π₀Functor.{u}.Monoidal := Functor.Monoidal.ofOplaxMonoidal _
  infer_instance

/-- The Cartesian monoidal structure of the component functor, derived from its
finite-product preservation, is available from the neutral product API. -/
noncomputable instance piZeroFunctorMonoidal : π₀Functor.{u}.Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

/-- The zero-factor product is covered by the genuine finite-product preservation instance. -/
theorem piZeroFunctor_preserves_zeroProduct :
    PreservesLimitsOfShape (Discrete (Fin 0)) (π₀Functor : SSet.{u} ⥤ Type u) := inferInstance

/-- Original component maps commute with the actual categorical product map. -/
theorem piZeroProductEquiv_natural {X' Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    (c : π₀ (X ⨯ Y)) :
    piZeroProductEquiv X' Y' (mapπ₀ (prod.map f g) c) =
      (mapπ₀ f (piZeroProductEquiv X Y c).1, mapπ₀ g (piZeroProductEquiv X Y c).2) := by
  rw [piZeroProductEquiv_apply, piZeroProductEquiv_apply]
  apply Prod.ext
  · change mapπ₀ (prod.fst : X' ⨯ Y' ⟶ X') (mapπ₀ (prod.map f g) c) =
      mapπ₀ f (mapπ₀ (prod.fst : X ⨯ Y ⟶ X) c)
    rw [← mapπ₀_comp_apply, prod.map_fst, mapπ₀_comp_apply]
  · change mapπ₀ (prod.snd : X' ⨯ Y' ⟶ Y') (mapπ₀ (prod.map f g) c) =
      mapπ₀ g (mapπ₀ (prod.snd : X ⨯ Y ⟶ Y) c)
    rw [← mapπ₀_comp_apply, prod.map_snd, mapπ₀_comp_apply]

end SSet
