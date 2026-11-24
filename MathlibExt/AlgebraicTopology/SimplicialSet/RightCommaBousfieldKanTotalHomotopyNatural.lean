/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanTotalReindex
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanPointFiberComparison

/-!
# Global right-comma Bousfield--Kan homotopy

This downstream layer assembles the degreewise right-comma prism into a map
of simplicial sets.  Naturality is proved on explicit weighted summands using
the arbitrary decoder formula and local prism naturality.

No realization, weak-equivalence, homotopy-fiber, or Quillen-Theorem-A claim
is made here.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Opposite Simplicial
open scoped Simplicial

namespace SSet

universe u v w

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

private theorem rightCommaBKIncl_exists (F : C ⥤ D) (n : ℕ)
    (z : (bkHocolim (rightCommaNerveDiagram F)).obj (op ⦋n⦌)) :
    ∃ (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
      (X : ((rightCommaNerveDiagram F).obj p.1.left).obj (op ⦋n⦌)),
      z = rightCommaBKIncl.{u, v, w} F n p X := by
  let y := (rightCommaTotalDegreeSigmaIso.{u, v, w} F n).hom z
  let p := y.1
  let X := y.2
  refine ⟨p, X, ?_⟩
  apply (rightCommaTotalDegreeSigmaIso.{u, v, w} F n).toEquiv.injective
  change (rightCommaTotalDegreeSigmaIso.{u, v, w} F n).hom z =
    (rightCommaTotalDegreeSigmaIso.{u, v, w} F n).hom
      (rightCommaBKIncl.{u, v, w} F n p X)
  have hIncl := ConcreteCategory.congr_hom
    (rightCommaTotalDegreeSigmaIso_hom_ι.{u, v, w} F n p) X
  change (rightCommaTotalDegreeSigmaIso.{u, v, w} F n).hom
      (rightCommaBKIncl.{u, v, w} F n p X) = ⟨p, X⟩ at hIncl
  exact (show (rightCommaTotalDegreeSigmaIso.{u, v, w} F n).hom z = ⟨p, X⟩ from rfl).trans
    hIncl.symm

/-- Inclusionwise naturality of the degreewise total cylinder. -/
theorem rightCommaTotalCylinderDegree_naturality_ι (F : C ⥤ D)
    {m n : ℕ} (k : op ⦋n⦌ ⟶ op ⦋m⦌)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (X : ((rightCommaNerveDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (t : (Δ[1] : SSet.{max u v w}).obj (op ⦋n⦌)) :
    rightCommaTotalCylinderDegree.{u, v, w} F m
        ⟨(bkHocolim (rightCommaNerveDiagram F)).map k
            (rightCommaBKIncl.{u, v, w} F n p X),
          (Δ[1] : SSet.{max u v w}).map k t⟩ =
      (nerve D).map k
        (rightCommaTotalCylinderDegree.{u, v, w} F n
          ⟨rightCommaBKIncl.{u, v, w} F n p X, t⟩) := by
  have hOld : rightCommaTotalCylinderDegree.{u, v, w} F n
      ⟨rightCommaBKIncl.{u, v, w} F n p X, t⟩ =
        rightCommaPrismSimplex.{u, v, w} F p.1 X t := by
    rw [rightCommaBKIncl_apply]
    exact rightCommaTotalCylinderDegree_ι.{u, v, w} F n p X t
  change rightCommaPrismSimplex.{u, v, w} F
      (((rightCommaTotalDegreeSigmaIso.{u, v, w} F m).hom
        ((bkHocolim (rightCommaNerveDiagram F)).map k
          (rightCommaBKIncl.{u, v, w} F n p X))).1.1)
      (((rightCommaTotalDegreeSigmaIso.{u, v, w} F m).hom
        ((bkHocolim (rightCommaNerveDiagram F)).map k
          (rightCommaBKIncl.{u, v, w} F n p X))).2)
      ((Δ[1] : SSet.{max u v w}).map k t) = _
  rw [rightCommaTotalDegreeSigmaIso_map_ι.{u, v, w} F k p X, hOld]
  exact (rightCommaPrismSimplex_naturality.{u, v, w} F k p.1 X t).symm

/-- The degreewise right-comma prisms assemble into a simplicial cylinder
map. -/
def rightCommaTotalCylinder (F : C ⥤ D) :
    bkHocolim (rightCommaNerveDiagram F) ⊗ (Δ[1] : SSet.{max u v w}) ⟶ nerve D where
  app a := by
    obtain ⟨⟨n⟩⟩ := a
    exact rightCommaTotalCylinderDegree.{u, v, w} F n
  naturality := by
    intro a b k
    obtain ⟨⟨n⟩⟩ := a
    obtain ⟨⟨m⟩⟩ := b
    change (↾fun x :
        (bkHocolim (rightCommaNerveDiagram F)).obj (op ⦋n⦌) ×
          (Δ[1] : SSet.{max u v w}).obj (op ⦋n⦌) =>
      rightCommaTotalCylinderDegree.{u, v, w} F m
        ⟨(bkHocolim (rightCommaNerveDiagram F)).map k x.1,
          (Δ[1] : SSet.{max u v w}).map k x.2⟩) =
      (↾fun x :
        (bkHocolim (rightCommaNerveDiagram F)).obj (op ⦋n⦌) ×
          (Δ[1] : SSet.{max u v w}).obj (op ⦋n⦌) =>
        (nerve D).map k (rightCommaTotalCylinderDegree.{u, v, w} F n x))
    apply ConcreteCategory.hom_ext
    rintro ⟨z, t⟩
    obtain ⟨p, X, hz⟩ := rightCommaBKIncl_exists.{u, v, w} F n z
    rw [hz]
    exact rightCommaTotalCylinderDegree_naturality_ι F k p X t

@[simp]
theorem rightCommaTotalCylinder_app_mk (F : C ⥤ D) (n : ℕ) :
    (rightCommaTotalCylinder.{u, v, w} F).app (op ⦋n⦌) =
      rightCommaTotalCylinderDegree.{u, v, w} F n :=
  rfl

/-- The total source map evaluated on the typed BK summand inclusion. -/
theorem rightCommaTotalToSource_BKIncl_apply (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (X : ((rightCommaNerveDiagram F).obj p.1.left).obj (op ⦋n⦌)) :
    (rightCommaTotalToSource.{u, v, w} F).app (op ⦋n⦌)
        (rightCommaBKIncl.{u, v, w} F n p X) =
      (nerveMapCross.{max v w, max u w} (rightCommaProjectionFunctor.{u, v, w} F p.1.left)).app
        (op ⦋n⦌) X := by
  have h := rightCommaTotalToSource_app_mk_ι F n p
  change (↾fun x => (rightCommaTotalToSource.{u, v, w} F).app (op ⦋n⦌)
      (rightCommaBKIncl.{u, v, w} F n p x)) =
    (nerveMapCross.{max v w, max u w} (rightCommaProjectionFunctor.{u, v, w} F p.1.left)).app
      (op ⦋n⦌) at h
  exact ConcreteCategory.congr_hom h X

/-- The total target map evaluated on the typed BK summand inclusion. -/
theorem rightCommaTotalToTarget_BKIncl_apply (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (X : ((rightCommaNerveDiagram F).obj p.1.left).obj (op ⦋n⦌)) :
    (rightCommaTotalToTarget.{u, v, w} F).app (op ⦋n⦌)
        (rightCommaBKIncl.{u, v, w} F n p X) =
      p.1 := by
  have h := rightCommaTotalToTarget_app_mk_ι F n p
  rw [bkPointIsoNerve_hom_wbarIncl (J := D) n p] at h
  exact congrArg (fun q => q X) h

/-- Zero endpoint formula on one weighted summand, expressed through the
total source map followed by `nerveMapCommonHom.{u, w, v} F`. -/
theorem rightCommaTotalCylinderDegree_ι_zero_total (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (X : ((rightCommaNerveDiagram F).obj p.1.left).obj (op ⦋n⦌)) :
    rightCommaTotalCylinderDegree.{u, v, w} F n
        ⟨rightCommaBKIncl.{u, v, w} F n p X, rightCommaPrismZero.{max u v w} n⟩ =
      (nerveMapCommonHom.{u, w, v} F).app (op ⦋n⦌)
        ((rightCommaTotalToSource.{u, v, w} F).app (op ⦋n⦌)
          (rightCommaBKIncl.{u, v, w} F n p X)) := by
  have hCylinder : rightCommaTotalCylinderDegree.{u, v, w} F n
      ⟨rightCommaBKIncl.{u, v, w} F n p X, rightCommaPrismZero.{max u v w} n⟩ =
        X ⋙ (rightCommaProjectionFunctor.{u, v, w} F p.1.left ⋙ F) := by
    rw [rightCommaBKIncl_apply]
    exact rightCommaTotalCylinderDegree_ι_zero.{u, v, w} F n p X
  have hSource := rightCommaTotalToSource_BKIncl_apply.{u, v, w} F n p X
  rw [hCylinder, hSource]
  change X ⋙ (rightCommaProjectionFunctor.{u, v, w} F p.1.left ⋙ F) =
    (X ⋙ rightCommaProjectionFunctor.{u, v, w} F p.1.left) ⋙ F
  exact (Functor.assoc X (rightCommaProjectionFunctor.{u, v, w} F p.1.left) F).symm

/-- One endpoint formula on one weighted summand, expressed through the
total target map. -/
theorem rightCommaTotalCylinderDegree_ι_one_total (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (X : ((rightCommaNerveDiagram F).obj p.1.left).obj (op ⦋n⦌)) :
    rightCommaTotalCylinderDegree.{u, v, w} F n
        ⟨rightCommaBKIncl.{u, v, w} F n p X, rightCommaPrismOne.{max u v w} n⟩ =
      (rightCommaTotalToTarget.{u, v, w} F).app (op ⦋n⦌)
        (rightCommaBKIncl.{u, v, w} F n p X) := by
  have hCylinder : rightCommaTotalCylinderDegree.{u, v, w} F n
      ⟨rightCommaBKIncl.{u, v, w} F n p X, rightCommaPrismOne.{max u v w} n⟩ =
        p.1 := by
    rw [rightCommaBKIncl_apply]
    exact rightCommaTotalCylinderDegree_ι_one.{u, v, w} F n p X
  exact hCylinder.trans
    (rightCommaTotalToTarget_BKIncl_apply.{u, v, w} F n p X).symm

/-- The zero endpoint of the global cylinder is the total comma projection
followed by `nerveMapCommonHom.{u, w, v} F`. -/
theorem rightCommaTotalCylinder_h₀ (F : C ⥤ D) :
    SSet.ι₀ ≫ rightCommaTotalCylinder.{u, v, w} F =
      rightCommaTotalToSource.{u, v, w} F ≫ nerveMapCommonHom.{u, w, v} F := by
  apply NatTrans.ext
  funext a
  obtain ⟨⟨n⟩⟩ := a
  change (↾fun z : (bkHocolim (rightCommaNerveDiagram F)).obj (op ⦋n⦌) =>
      rightCommaTotalCylinderDegree.{u, v, w} F n
        ⟨z, rightCommaPrismZero.{max u v w} n⟩) =
    (↾fun z : (bkHocolim (rightCommaNerveDiagram F)).obj (op ⦋n⦌) =>
      (nerveMapCommonHom.{u, w, v} F).app (op ⦋n⦌)
        ((rightCommaTotalToSource.{u, v, w} F).app (op ⦋n⦌) z))
  apply ConcreteCategory.hom_ext
  intro z
  obtain ⟨p, X, hz⟩ := rightCommaBKIncl_exists.{u, v, w} F n z
  rw [hz]
  exact rightCommaTotalCylinderDegree_ι_zero_total.{u, v, w} F n p X

/-- The one endpoint of the global cylinder is the total map to the indexing
nerve. -/
theorem rightCommaTotalCylinder_h₁ (F : C ⥤ D) :
    SSet.ι₁ ≫ rightCommaTotalCylinder.{u, v, w} F =
      rightCommaTotalToTarget.{u, v, w} F := by
  apply NatTrans.ext
  funext a
  obtain ⟨⟨n⟩⟩ := a
  change (↾fun z : (bkHocolim (rightCommaNerveDiagram F)).obj (op ⦋n⦌) =>
      rightCommaTotalCylinderDegree.{u, v, w} F n
        ⟨z, rightCommaPrismOne.{max u v w} n⟩) =
    (rightCommaTotalToTarget.{u, v, w} F).app (op ⦋n⦌)
  apply ConcreteCategory.hom_ext
  intro z
  obtain ⟨p, X, hz⟩ := rightCommaBKIncl_exists.{u, v, w} F n z
  rw [hz]
  exact rightCommaTotalCylinderDegree_ι_one_total.{u, v, w} F n p X

/-- The global model-independent homotopy from the comma-total source route
to the canonical map to the target nerve. -/
def rightCommaTotalHomotopy (F : C ⥤ D) :
    SSet.Homotopy
      (rightCommaTotalToSource.{u, v, w} F ≫ nerveMapCommonHom.{u, w, v} F)
      (rightCommaTotalToTarget.{u, v, w} F) where
  h := rightCommaTotalCylinder.{u, v, w} F
  h₀ := rightCommaTotalCylinder_h₀.{u, v, w} F
  h₁ := rightCommaTotalCylinder_h₁.{u, v, w} F
  rel := by
    ext n ⟨⟨x, hx⟩, t⟩
    cases hx

end SSet

end
