/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanPrismReindex
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Degreewise cylinder for the right-comma BK total

In diagonal degree `n`, the Bousfield--Kan carrier is an evaluated
functor-category coproduct.  The canonical evaluation and Type-coproduct
isomorphisms decode it as a dependent sum of weighted chains and inner comma
simplices.  Applying `rightCommaPrismSimplex` on each summand gives the
degree-`n` cylinder function.

This file initially records only the degreewise map, its weighted-summand
formula, and the all-zero/all-one formulas on each summand.  It makes no
global simplicial homotopy, realization, weak-equivalence, homotopy-fiber, or
Quillen-Theorem-A claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Simplicial
open scoped Simplicial

namespace SSet

universe u v w

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

/-- Decode a diagonal BK degree into a weighted outer chain and an inner
right-comma simplex. -/
def rightCommaTotalDegreeSigmaIso (F : C ⥤ D) (n : ℕ) :
    (bkHocolim (rightCommaNerveDiagram F)).obj (op ⦋n⦌) ≅
      (Σ p : StrictOrdinaryWeightedBar.WIdx D
          (CategoryBar.replUnit D) n,
        ((rightCommaNerveDiagram F).obj p.1.left).obj (op ⦋n⦌)) :=
  Limits.sigmaObjIso
      (fun p : StrictOrdinaryWeightedBar.WIdx D
        (CategoryBar.replUnit D) n =>
          (rightCommaNerveDiagram F).obj p.1.left) (op ⦋n⦌) ≪≫
    Limits.Types.coproductIso
      (fun p : StrictOrdinaryWeightedBar.WIdx D
        (CategoryBar.replUnit D) n =>
          ((rightCommaNerveDiagram F).obj p.1.left).obj (op ⦋n⦌))

/-- The degree decoder sends a weighted-bar inclusion to the corresponding
dependent-pair constructor. -/
theorem rightCommaTotalDegreeSigmaIso_hom_ι (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit D) (rightCommaNerveDiagram F) n p).app
          (op ⦋n⦌) ≫
      (rightCommaTotalDegreeSigmaIso.{u, v, w} F n).hom =
    ↾fun x => ⟨p, x⟩ := by
  change
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit D) (rightCommaNerveDiagram F) n p).app
          (op ⦋n⦌) ≫
      ((Limits.sigmaObjIso
          (fun p : StrictOrdinaryWeightedBar.WIdx D
            (CategoryBar.replUnit D) n =>
              (rightCommaNerveDiagram F).obj p.1.left) (op ⦋n⦌)).hom ≫
        (Limits.Types.coproductIso
          (fun p : StrictOrdinaryWeightedBar.WIdx D
            (CategoryBar.replUnit D) n =>
              ((rightCommaNerveDiagram F).obj p.1.left).obj
                (op ⦋n⦌))).hom) = _
  calc
    _ = ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit D) (rightCommaNerveDiagram F) n p).app
            (op ⦋n⦌) ≫
        (Limits.sigmaObjIso
          (fun p : StrictOrdinaryWeightedBar.WIdx D
            (CategoryBar.replUnit D) n =>
              (rightCommaNerveDiagram F).obj p.1.left) (op ⦋n⦌)).hom) ≫
      (Limits.Types.coproductIso
        (fun p : StrictOrdinaryWeightedBar.WIdx D
          (CategoryBar.replUnit D) n =>
            ((rightCommaNerveDiagram F).obj p.1.left).obj
              (op ⦋n⦌))).hom := (Category.assoc _ _ _).symm
    _ = Limits.Sigma.ι
        (fun p : StrictOrdinaryWeightedBar.WIdx D
          (CategoryBar.replUnit D) n =>
            ((rightCommaNerveDiagram F).obj p.1.left).obj (op ⦋n⦌)) p ≫
      (Limits.Types.coproductIso
        (fun p : StrictOrdinaryWeightedBar.WIdx D
          (CategoryBar.replUnit D) n =>
            ((rightCommaNerveDiagram F).obj p.1.left).obj
              (op ⦋n⦌))).hom :=
      congrArg (· ≫ (Limits.Types.coproductIso
        (fun p : StrictOrdinaryWeightedBar.WIdx D
          (CategoryBar.replUnit D) n =>
            ((rightCommaNerveDiagram F).obj p.1.left).obj
              (op ⦋n⦌))).hom)
        (Limits.ι_comp_sigmaObjIso_hom _ _ p)
    _ = ↾fun x => ⟨p, x⟩ :=
      Limits.Types.coproductIso_ι_comp_hom _ p

/-- Degree-`n` map of the mixed right-comma BK cylinder. -/
def rightCommaTotalCylinderDegree (F : C ⥤ D) (n : ℕ) :
    (bkHocolim (rightCommaNerveDiagram F) ⊗ (Δ[1] : SSet.{max u v w})).obj
        (op ⦋n⦌) ⟶
      (nerve D).obj (op ⦋n⦌) :=
  ↾fun z =>
    let y := (rightCommaTotalDegreeSigmaIso.{u, v, w} F n).hom z.1
    rightCommaPrismSimplex.{u, v, w} F y.1.1 y.2 z.2

/-- The degreewise cylinder restricts on each weighted summand to the local
right-comma prism. -/
theorem rightCommaTotalCylinderDegree_ι (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (X : ((rightCommaNerveDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (t : (Δ[1] : SSet.{max u v w}).obj (op ⦋n⦌)) :
    rightCommaTotalCylinderDegree.{u, v, w} F n
        ⟨(StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit D) (rightCommaNerveDiagram F) n p).app
            (op ⦋n⦌) X, t⟩ =
      rightCommaPrismSimplex.{u, v, w} F p.1 X t := by
  have h := ConcreteCategory.congr_hom
    (rightCommaTotalDegreeSigmaIso_hom_ι.{u, v, w} F n p) X
  change (rightCommaTotalDegreeSigmaIso.{u, v, w} F n).hom
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit D) (rightCommaNerveDiagram F) n p).app
          (op ⦋n⦌) X) = ⟨p, X⟩ at h
  change rightCommaPrismSimplex.{u, v, w} F
      (((rightCommaTotalDegreeSigmaIso.{u, v, w} F n).hom
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit D) (rightCommaNerveDiagram F) n p).app
            (op ⦋n⦌) X)).1.1)
      (((rightCommaTotalDegreeSigmaIso.{u, v, w} F n).hom
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit D) (rightCommaNerveDiagram F) n p).app
            (op ⦋n⦌) X)).2) t =
    rightCommaPrismSimplex.{u, v, w} F p.1 X t
  rw [h]

/-- All-zero endpoint formula on a weighted summand. -/
theorem rightCommaTotalCylinderDegree_ι_zero (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (X : ((rightCommaNerveDiagram F).obj p.1.left).obj (op ⦋n⦌)) :
    rightCommaTotalCylinderDegree.{u, v, w} F n
        ⟨(StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit D) (rightCommaNerveDiagram F) n p).app
            (op ⦋n⦌) X, rightCommaPrismZero.{max u v w} n⟩ =
      X ⋙ (rightCommaProjectionFunctor.{u, v, w} F p.1.left ⋙ F) := by
  rw [rightCommaTotalCylinderDegree_ι]
  exact rightCommaPrismSimplex_zero.{u, v, w} F p.1 X

/-- All-one endpoint formula on a weighted summand. -/
theorem rightCommaTotalCylinderDegree_ι_one (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (X : ((rightCommaNerveDiagram F).obj p.1.left).obj (op ⦋n⦌)) :
    rightCommaTotalCylinderDegree.{u, v, w} F n
        ⟨(StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit D) (rightCommaNerveDiagram F) n p).app
            (op ⦋n⦌) X, rightCommaPrismOne.{max u v w} n⟩ =
      p.1 := by
  rw [rightCommaTotalCylinderDegree_ι]
  exact rightCommaPrismSimplex_one.{u, v, w} F p.1 X

end SSet

end
