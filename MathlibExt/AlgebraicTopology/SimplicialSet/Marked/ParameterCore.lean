/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingFibrancy
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Constants
import MathlibExt.AlgebraicTopology.SimplicialSet.LeftIhomEvaluation
import MathlibExt.AlgebraicTopology.Quasicategory.PointwiseCore

/-!
# The native core criterion for whole left-parameter prisms

The already proved pointwise internal-Hom equivalence criterion detects
equivalence edges by their original source-vertex evaluations. In the
left-prism dictionary these are exactly the vertical original edges.
Applying the criterion to every parameter edge gives the all-degree native
core condition, with no restriction on the original source simplicial set.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

namespace SSet.Marked

private theorem const_one_eq_sigma {X : SSet.{u}} (x : X _⦋0⦌) :
    X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op x = X.σ (0 : Fin 1) x := by
  exact const_app_one (X := min (Δ[1] : SSet.{u})) (Y := min X) x
    (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))

/-- A whole parameter edge is an equivalence exactly when every original vertical evaluation is. -/
theorem parameter_edge_isEquivalence_iff {X Y : SSet.{u}} [Quasicategory Y]
    (F : (Δ[1] : SSet.{u}) ⊗ X ⟶ Y) :
    (Edge.mk' (X := parameterMapping X Y) F).IsEquivalence ↔
    ∀ x : X _⦋0⦌, (Edge.mk' (F.app (op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), X.σ (0 : Fin 1) x))).IsEquivalence := by
  let e := Edge.mk' (X := parameterMapping X Y) F
  let q := parameterMappingIsoIhom X Y
  have hev (x : X _⦋0⦌) :
      (((e.map q.hom).map ((pre (SSet.yonedaEquiv.symm x)).app Y)).map
        (evalDeltaZeroIso Y).hom).edge =
      F.app (op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), X.σ (0 : Fin 1) x) := by
    change (((pre (SSet.yonedaEquiv.symm x)).app Y ≫ (evalDeltaZeroIso Y).hom).app (op ⦋1⦌))
      (leftIhomSimplexOfPrism F) = _
    rw [eval_leftIhomSimplexOfPrism, const_one_eq_sigma]
  constructor
  · intro h x
    have hi := (Edge.isEquivalence_iff_forall_eval_vertex (e.map q.hom)).mp (h.map q.hom) x
    exact hi.of_edge_eq (hev x)
  · intro h
    have hi : (e.map q.hom).IsEquivalence :=
      (Edge.isEquivalence_iff_forall_eval_vertex (e.map q.hom)).mpr
        (fun x => (h x).of_edge_eq (hev x).symm)
    have hb := hi.map q.inv
    have he : ((e.map q.hom).map q.inv).edge = e.edge := by
      change leftIhomPrismOfSimplex (leftIhomSimplexOfPrism F) = F
      exact leftIhomPrismOfSimplex_simplex F
    exact hb.of_edge_eq he

/-- The native core of the original prism complex consists exactly of prisms with equivalent vertical edges. -/
theorem mem_core_parameterMapping_iff {X Y : SSet.{u}} [Quasicategory Y] {n : ℕ}
    (F : (Δ[n] : SSet.{u}) ⊗ X ⟶ Y) :
    F ∈ (core (parameterMapping X Y)).obj (op ⦋n⦌) ↔
    ∀ (a : (Δ[n] : SSet.{u}) _⦋1⦌) (x : X _⦋0⦌),
      (Edge.mk' (F.app (op ⦋1⦌) (a, X.σ (0 : Fin 1) x))).IsEquivalence := by
  constructor
  · intro h a x
    let φ := SSet.stdSimplex.objEquiv a
    have hv := (parameter_edge_isEquivalence_iff ((SSet.stdSimplex.map φ ▷ X) ≫ F)).mp (h φ) x
    have hp : (SSet.stdSimplex.map φ).app (op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) = a := by
      change SSet.yonedaEquiv (SSet.stdSimplex.map φ) = a
      rw [SSet.yonedaEquiv_map]
      exact Equiv.symm_apply_apply _ a
    exact hv.of_edge_eq (congrArg (fun b => F.app (op ⦋1⦌) (b, X.σ (0 : Fin 1) x)) hp)
  · intro h φ
    apply (parameter_edge_isEquivalence_iff ((SSet.stdSimplex.map φ ▷ X) ≫ F)).mpr
    intro x
    have hp : (SSet.stdSimplex.map φ).app (op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) = SSet.stdSimplex.objEquiv.symm φ :=
      SSet.yonedaEquiv_map φ
    exact (h (SSet.stdSimplex.objEquiv.symm φ) x).of_edge_eq
      (congrArg (fun b => F.app (op ⦋1⦌) (b, X.σ (0 : Fin 1) x)) hp).symm

end SSet.Marked
