/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeCartesianPrismBoundary
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Triangle
import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.Triangle
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Interval
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Products
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Fibrations

/-!
# Complete endpoint-prism markings from the actual critical verticals

The two original product triangles transport a Cartesian marking from the
target row, or a cocartesian marking from the source row, to every mixed
marked edge. The only interval edges are its two original degeneracies
and its actual fundamental edge. All these edge images and the original
full prism are retained; no equivalence condition on the critical
verticals is added.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- A row of the actual prism reads exactly the original constant endpoint edge in degree one. -/
theorem prismSectionAt_app_one {T E : SSet.{u}} (F : T ⊗ Δ[1] ⟶ E)
    (ε : Fin 2) (a : T _⦋1⦌) :
    (prismSectionAt T ε ≫ F).app (op ⦋1⦌) a =
      F.app (op ⦋1⦌) (a, (Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm ε)) := by
  apply congrArg (F.app (op ⦋1⦌))
  apply Prod.ext
  · rfl
  · apply stdSimplex.ext
    intro i
    fin_cases i <;> rfl

private abbrev intervalFundamental : Edge
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2) : (Δ[1] : SSet.{u}) _⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
  Edge.mk (yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
    (by apply stdSimplex.ext; intro i; fin_cases i; rfl)
    (by apply stdSimplex.ext; intro i; fin_cases i; rfl)

private theorem interval_edges_induction (P : (Δ[1] : SSet.{u}) _⦋1⦌ → Prop)
    (hzero : P ((Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (hfundamental : P intervalFundamental.{u}.edge)
    (hone : P ((Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (b : (Δ[1] : SSet.{u}) _⦋1⦌) : P b := by
  obtain ⟨j, hj⟩ := stdSimplex.objMk₁_surjective b
  apply (congrArg P hj).to_iff.mp
  fin_cases j
  · have he : stdSimplex.objMk₁.{u} (0 : Fin 3) =
        (Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
      apply stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    exact (congrArg P he).to_iff.mpr hone
  · have he : stdSimplex.objMk₁.{u} (1 : Fin 3) = intervalFundamental.{u}.edge := by
      apply stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    exact (congrArg P he).to_iff.mpr hfundamental
  · have he : stdSimplex.objMk₁.{u} (2 : Fin 3) =
        (Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
      apply stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    exact (congrArg P he).to_iff.mpr hzero

/-- The two actual product triangles give the mixed Cartesian edge and source row from the target row and
  Cartesian verticals. -/
theorem cartesian_mixed_and_source_of_target {T I E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B] (F : T ⊗ I ⟶ E)
    {t₀ t₁ : T _⦋0⦌} (a : Edge t₀ t₁) {i₀ i₁ : I _⦋0⦌} (b : Edge i₀ i₁)
    (hv₀ : CartesianEdge.IsPCartesian p (yonedaEquiv.symm (((Edge.id t₀).tensor b).map F).edge))
    (hv₁ : CartesianEdge.IsPCartesian p (yonedaEquiv.symm (((Edge.id t₁).tensor b).map F).edge))
    (hh₁ : CartesianEdge.IsPCartesian p (yonedaEquiv.symm ((a.tensor (Edge.id i₁)).map F).edge)) :
    CartesianEdge.IsPCartesian p (yonedaEquiv.symm ((a.tensor b).map F).edge) ∧
      CartesianEdge.IsPCartesian p (yonedaEquiv.symm ((a.tensor (Edge.id i₀)).map F).edge) := by
  let H := ((Edge.CompStruct.idComp a).tensor (Edge.CompStruct.compId b)).map F
  let H' := ((Edge.CompStruct.compId a).tensor (Edge.CompStruct.idComp b)).map F
  have hd := CartesianEdge.isPCartesian_of_compStruct p H hv₀ hh₁
  exact ⟨hd, (CartesianEdge.isPCartesian_iff_of_compStruct p H' hv₁).mpr hd⟩

/-- Actual cocartesian verticals and the source row determine both the mixed edge and target row through the
  original product triangles. -/
theorem cocartesian_mixed_and_target_of_source {T I E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B] (F : T ⊗ I ⟶ E)
    {t₀ t₁ : T _⦋0⦌} (a : Edge t₀ t₁) {i₀ i₁ : I _⦋0⦌} (b : Edge i₀ i₁)
    (hv₀ : CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm (((Edge.id t₀).tensor b).map F).edge))
    (hv₁ : CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm (((Edge.id t₁).tensor b).map F).edge))
    (hh₀ : CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm ((a.tensor (Edge.id i₀)).map F).edge)) :
    CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm ((a.tensor b).map F).edge) ∧
      CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm ((a.tensor (Edge.id i₁)).map F).edge) := by
  let H := ((Edge.CompStruct.idComp a).tensor (Edge.CompStruct.compId b)).map F
  let H' := ((Edge.CompStruct.compId a).tensor (Edge.CompStruct.idComp b)).map F
  have hd := CocartesianEdge.isPCocartesian_of_compStruct p H' hh₀ hv₁
  exact ⟨hd, (CocartesianEdge.isPCocartesian_iff_of_compStruct p H hv₀).mpr hd⟩

/-- The whole original prism is a marked map when its critical verticals and target-row marked edges are Cartesian. -/
def markedCartesianPrismOfTarget {T : Marked.{u}} {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] (F : T.toSSet ⊗ Δ[1] ⟶ E)
    (hv : PrismOneVerticalsCartesian p F)
    (hrow : ∀ a : T.toSSet _⦋1⦌, a ∈ T.marking →
      CartesianEdge.IsPCartesian p (yonedaEquiv.symm
        ((prismSectionAt T.toSSet (1 : Fin 2) ≫ F).app (op ⦋1⦌) a))) :
    prod T (max (Δ[1] : SSet.{u})) ⟶ cartesian p where
  hom := F
  preserve {z} hz := by
    let a : T.toSSet _⦋1⦌ := z.1
    let b : (Δ[1] : SSet.{u}) _⦋1⦌ := z.2
    let P : (Δ[1] : SSet.{u}) _⦋1⦌ → Prop :=
      fun t => CartesianEdge.IsPCartesian p (yonedaEquiv.symm (F.app (op ⦋1⦌) (a, t)))
    have hrow' := hrow a hz.1
    rw [prismSectionAt_app_one] at hrow'
    have h := cartesian_mixed_and_source_of_target p F (Edge.mk' a) intervalFundamental
      (hv _) (hv _) hrow'
    exact interval_edges_induction P h.2 h.1 hrow' b

/-- The original dual prism carries all mixed marked edges from its cocartesian verticals and source row. -/
def markedCocartesianPrismOfSource {T : Marked.{u}} {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] (F : T.toSSet ⊗ Δ[1] ⟶ E)
    (hv : PrismOneVerticalsCocartesian p F)
    (hrow : ∀ a : T.toSSet _⦋1⦌, a ∈ T.marking →
      CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm
        ((prismSectionAt T.toSSet (0 : Fin 2) ≫ F).app (op ⦋1⦌) a))) :
    prod T (max (Δ[1] : SSet.{u})) ⟶ cocartesian p where
  hom := F
  preserve {z} hz := by
    let a : T.toSSet _⦋1⦌ := z.1
    let b : (Δ[1] : SSet.{u}) _⦋1⦌ := z.2
    let P : (Δ[1] : SSet.{u}) _⦋1⦌ → Prop :=
      fun t => CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm (F.app (op ⦋1⦌) (a, t)))
    have hrow' := hrow a hz.1
    rw [prismSectionAt_app_one] at hrow'
    have h := cocartesian_mixed_and_target_of_source p F (Edge.mk' a) intervalFundamental
      (hv _) (hv _) hrow'
    exact interval_edges_induction P hrow' h.1 h.2 b

end SSet.Marked
