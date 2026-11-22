/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.GammaDiagram
public import MathlibExt.AlgebraicTopology.Quasicategory.CoreFunctor

/-!
# Gamma's literal zero space and the native quasicategory core

The actual Gamma diagram has outer degree zero `core(Q^Δ[0])`. Applying
the existing equivalence-edge core functor to the native evaluation
isomorphism `Q^Δ[0] ≅ Q` identifies this space with `core Q`. The maps
are the original restricted simplicial maps, and the vertex comparison
agrees with Gamma's existing zeroth-row isomorphism and adjunction unit.
The isomorphism is raw: Gamma fibrancy for quasicategories and comparison
with an arbitrary complete Segal presentation are separate results.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite MonoidalClosed
open scoped Simplicial

namespace SSet.Rezk

/-- Gamma's original zero space is identified with the native core by evaluation at Δ[0]. -/
def gammaZeroCoreIso (Q : SSet.{u}) :
    (gammaDiagram.obj Q).obj (op ⦋0⦌) ≅ (core Q : SSet.{u}) :=
  coreFunctor.mapIso (evalDeltaZeroIso Q)

/-- The forward map is the native restricted evaluation map. -/
theorem gammaZeroCoreIso_hom (Q : SSet.{u}) :
    (gammaZeroCoreIso Q).hom = core.map (evalDeltaZeroIso Q).hom := rfl

/-- The inverse is the restriction of the same native presentation inverse. -/
theorem gammaZeroCoreIso_inv (Q : SSet.{u}) :
    (gammaZeroCoreIso Q).inv = core.map (evalDeltaZeroIso Q).inv := rfl

/-- The comparison retains the literal underlying simplex map through the native inclusions. -/
theorem gammaZeroCoreIso_hom_ι (Q : SSet.{u}) :
    (gammaZeroCoreIso Q).hom ≫ (core Q).ι =
      (core ((ihom (Δ[0] : SSet.{u})).obj Q)).ι ≫ (evalDeltaZeroIso Q).hom :=
  core.map_ι (evalDeltaZeroIso Q).hom

/-- Each simplex is sent by the original evaluation, without changing its representative. -/
theorem gammaZeroCoreIso_hom_app_val (Q : SSet.{u}) (n : ℕ)
    (x : (core ((ihom (Δ[0] : SSet.{u})).obj Q) : SSet.{u}) _⦋n⦌) :
    (((gammaZeroCoreIso Q).hom).app (op ⦋n⦌) x).1 =
      ((evalDeltaZeroIso Q).hom).app (op ⦋n⦌) x.1 := by
  change (((core.map (evalDeltaZeroIso Q).hom).app (op ⦋n⦌)) x).1 = _
  rfl

/-- Target naturality is exactly the existing scalar evaluation naturality followed by core. -/
theorem gammaZeroCoreIso_natural {Q Q' : SSet.{u}} (f : Q ⟶ Q') :
    (gammaDiagram.map f).app (op ⦋0⦌) ≫ (gammaZeroCoreIso Q').hom =
      (gammaZeroCoreIso Q).hom ≫ core.map f := by
  change core.map ((ihom (Δ[0] : SSet.{u})).map f) ≫
      core.map (evalDeltaZeroIso Q').hom =
    core.map (evalDeltaZeroIso Q).hom ≫ core.map f
  rw [← core.map_comp, ← core.map_comp, evalDeltaZeroIso_hom_natural]

/-- The original zero-space comparison is natural in every simplicial set. -/
def gammaZeroCoreNatIso :
    gammaDiagram.{u} ⋙
      (CategoryTheory.evaluation SimplexCategoryᵒᵖ SSet.{u}).obj (op ⦋0⦌) ≅
        coreFunctor.{u} :=
  NatIso.ofComponents gammaZeroCoreIso (fun f => gammaZeroCoreIso_natural f)

/-- At original vertices, the core comparison equals the existing Gamma row identification. -/
theorem gammaZeroCoreIso_vertex_row (Q : SSet.{u})
    (x : ((gammaDiagram.obj Q).obj (op ⦋0⦌)) _⦋0⦌) :
    (((gammaZeroCoreIso Q).hom).app (op ⦋0⦌) x).1 =
      (gammaZerothRowIso.hom.app Q).app (op ⦋0⦌) x := by
  obtain ⟨q, hq⟩ := (ihomVertexEquiv (Δ[0] : SSet.{u}) Q).surjective x.1
  have hx : x = ⟨ihomVertexEquiv (Δ[0] : SSet.{u}) Q q, mem_core_obj_zero _⟩ :=
    Subtype.ext hq.symm
  subst x
  exact (gammaZeroCoreIso_hom_app_val Q 0 _).trans
    ((evalDeltaZeroIso_hom_app_ihomVertexEquiv q).trans
      (gammaZerothRowIso_hom_app Q (op ⦋0⦌) q).symm)

/-- The actual Gamma adjunction unit followed by this core comparison retains each original object. -/
theorem gammaZeroCoreIso_unit_vertex (Q : SSet.{u}) (x : Q _⦋0⦌) :
    (((gammaZeroCoreIso Q).hom).app (op ⦋0⦌)
      (((gammaUnit.app Q).app (op ⦋0⦌)).app (op ⦋0⦌) x)).1 = x := by
  have h := ConcreteCategory.congr_hom
    (congr_app (gammaUnit_row_hom Q) (op ⦋0⦌)) x
  change (gammaZerothRowIso.hom.app Q).app (op ⦋0⦌)
    (((gammaUnit.app Q).app (op ⦋0⦌)).app (op ⦋0⦌) x) = x at h
  exact (gammaZeroCoreIso_vertex_row Q _).trans h

end SSet.Rezk
