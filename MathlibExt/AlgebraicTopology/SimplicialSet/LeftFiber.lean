/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Left fibers of simplicial maps

For a simplicial map `f : X ⟶ Y` and an `m`-simplex `y` of `Y`, the left
fiber `f / (m, y)` is the pullback of `f` along the Yoneda map
`Delta[m] ⟶ Y` represented by `y`.

An `a`-simplex is equivalently a pair consisting of `x : X.obj a` and a
simplex-category map `alpha : a.unop ⟶ [m]` such that
`f(x) = alpha^* y`.  The equivalence below records this description and
its exact behavior under simplicial reindexing.

This file only supplies the pullback object and its simplex-level API.  It
makes no strict-vertex-fiber, weak-equivalence, Quillen Theorem A, realization,
Kan, basepoint, Waldhausen, or additivity claim.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace SSet

/-- The left fiber of `f : X ⟶ Y` over the simplex `y : Y _[m]`, defined
as the pullback of `f` along the Yoneda map represented by `y`. -/
noncomputable def leftFiber {X Y : SSet.{u}} (f : X ⟶ Y) {m : ℕ}
    (y : Y _⦋m⦌) : SSet.{u} :=
  pullback f (SSet.yonedaEquiv.symm y)

namespace leftFiber

variable {X Y : SSet.{u}} (f : X ⟶ Y) {m : ℕ} (y : Y _⦋m⦌)

/-- Projection from the left fiber to the source simplicial set. -/
noncomputable def π : leftFiber f y ⟶ X :=
  pullback.fst f (SSet.yonedaEquiv.symm y)

/-- Projection from the left fiber to the representing standard simplex. -/
noncomputable def toSimplex : leftFiber f y ⟶ Δ[m] :=
  pullback.snd f (SSet.yonedaEquiv.symm y)

/-- The two projections satisfy the defining pullback equation. -/
@[reassoc (attr := simp)]
theorem condition :
    π f y ≫ f = toSimplex f y ≫ SSet.yonedaEquiv.symm y :=
  pullback.condition

/-- Arbitrary-degree simplices of a left fiber are pairs `(x, alpha)` such
that `f(x) = alpha^* y`. -/
noncomputable def objEquiv (a : SimplexCategoryᵒᵖ) :
    (leftFiber f y).obj a ≃
      {p : X.obj a × (a.unop ⟶ ⦋m⦌) //
        f.app a p.1 = Y.map p.2.op y} := by
  let yMap : Δ[m] ⟶ Y := SSet.yonedaEquiv.symm y
  let ePullback :
      (pullback f yMap).obj a ≃
        Types.PullbackObj (f.app a) (yMap.app a) :=
    ((pullbackObjIso f yMap a).trans
      (Types.pullbackIsoPullback (f.app a) (yMap.app a))).toEquiv
  let eProd :
      X.obj a × (Δ[m] : SSet.{u}).obj a ≃
        X.obj a × (a.unop ⟶ ⦋m⦌) :=
    Equiv.prodCongr (Equiv.refl _) SSet.stdSimplex.objEquiv
  exact ePullback.trans (eProd.subtypeEquiv (fun p => by
    change
      (f.app a p.1 = (SSet.yonedaEquiv.symm y).app a p.2) ↔
        f.app a p.1 = Y.map (SSet.stdSimplex.objEquiv p.2).op y
    rfl))

/-- The first coordinate of `objEquiv` is the source projection. -/
@[simp]
theorem objEquiv_fst (a : SimplexCategoryᵒᵖ)
    (z : (leftFiber f y).obj a) :
    ((objEquiv f y a z).1).1 = (π f y).app a z := by
  change
    (((Types.pullbackIsoPullback (f.app a)
      ((SSet.yonedaEquiv.symm y).app a)).hom
        ((pullbackObjIso f (SSet.yonedaEquiv.symm y) a).hom z)).1 :
          X.obj a × (Δ[m] : SSet.{u}).obj a).1 = _
  rw [Types.pullbackIsoPullback_hom_fst]
  exact ConcreteCategory.congr_hom
    (pullbackObjIso_hom_comp_fst f (SSet.yonedaEquiv.symm y) a) z

/-- The second coordinate of `objEquiv` is the simplex represented by the
standard-simplex projection. -/
@[simp]
theorem objEquiv_snd (a : SimplexCategoryᵒᵖ)
    (z : (leftFiber f y).obj a) :
    ((objEquiv f y a z).1).2 =
      SSet.stdSimplex.objEquiv ((toSimplex f y).app a z) := by
  change SSet.stdSimplex.objEquiv
      ((((Types.pullbackIsoPullback (f.app a)
        ((SSet.yonedaEquiv.symm y).app a)).hom
          ((pullbackObjIso f (SSet.yonedaEquiv.symm y) a).hom z)).1 :
            X.obj a × (Δ[m] : SSet.{u}).obj a).2) = _
  apply congrArg SSet.stdSimplex.objEquiv
  rw [Types.pullbackIsoPullback_hom_snd]
  exact ConcreteCategory.congr_hom
    (pullbackObjIso_hom_comp_snd f (SSet.yonedaEquiv.symm y) a) z

/-- Reindexing a left-fiber simplex sends `(x, alpha)` to
`(X.map k x, k.unop ≫ alpha)`. -/
@[simp]
theorem objEquiv_map {a b : SimplexCategoryᵒᵖ} (k : a ⟶ b)
    (z : (leftFiber f y).obj a) :
    objEquiv f y b ((leftFiber f y).map k z) =
      ⟨⟨X.map k ((objEquiv f y a z).1.1),
          k.unop ≫ (objEquiv f y a z).1.2⟩,
        by
          calc
            f.app b (X.map k ((objEquiv f y a z).1.1)) =
                Y.map k (f.app a ((objEquiv f y a z).1.1)) := by
              have h := ConcreteCategory.congr_hom
                (f.naturality k) ((π f y).app a z)
              change f.app b (X.map k ((π f y).app a z)) =
                Y.map k (f.app a ((π f y).app a z)) at h
              simpa only [objEquiv_fst] using h
            _ = Y.map k (Y.map ((objEquiv f y a z).1.2).op y) := by
              rw [(objEquiv f y a z).2]
            _ = Y.map (k.unop ≫ (objEquiv f y a z).1.2).op y := by
              have h := ConcreteCategory.congr_hom
                (Y.map_comp ((objEquiv f y a z).1.2).op k) y
              change Y.map
                  (((objEquiv f y a z).1.2).op ≫ k) y =
                Y.map k (Y.map ((objEquiv f y a z).1.2).op y) at h
              exact h.symm⟩ := by
  have hfst :
      ((objEquiv f y b ((leftFiber f y).map k z)).1).1 =
        X.map k ((objEquiv f y a z).1.1) := by
    have h := ConcreteCategory.congr_hom ((π f y).naturality k) z
    change (π f y).app b ((leftFiber f y).map k z) =
      X.map k ((π f y).app a z) at h
    simpa only [objEquiv_fst] using h
  have hsnd :
      ((objEquiv f y b ((leftFiber f y).map k z)).1).2 =
        k.unop ≫ (objEquiv f y a z).1.2 := by
    have h := ConcreteCategory.congr_hom ((toSimplex f y).naturality k) z
    change (toSimplex f y).app b ((leftFiber f y).map k z) =
      (Δ[m] : SSet.{u}).map k ((toSimplex f y).app a z) at h
    calc
      ((objEquiv f y b ((leftFiber f y).map k z)).1).2 =
          SSet.stdSimplex.objEquiv
            ((toSimplex f y).app b ((leftFiber f y).map k z)) :=
        objEquiv_snd f y b _
      _ = SSet.stdSimplex.objEquiv
          ((Δ[m] : SSet.{u}).map k ((toSimplex f y).app a z)) := by
        rw [h]
      _ = k.unop ≫ SSet.stdSimplex.objEquiv
          ((toSimplex f y).app a z) := by
        rw [SSet.stdSimplex.map_apply, Equiv.apply_symm_apply]
      _ = k.unop ≫ (objEquiv f y a z).1.2 := by
        rw [objEquiv_snd]
  apply Subtype.ext
  exact Prod.ext hfst hsnd

end leftFiber

end SSet

end
