/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialObjectHomotopy

/-!
# Whole-cylinder naturality of the combinatorial homotopy adapter

An original transformation of the source and target carries every original
homotopy face to the corresponding target face. The resulting actual
interval-cylinder maps commute on every original simplex and interval cut.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject.Homotopy

/-- Whole original homotopy-face naturality implies naturality of the literal cylinder adapter. -/
theorem toSSetHomotopyMap_naturality {X Y X' Y' : SSet.{u}}
    {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}
    (H : SimplicialObject.Homotopy f g) (H' : SimplicialObject.Homotopy f' g')
    (p : X ⟶ X') (q : Y ⟶ Y')
    (hg : p ≫ g' = g ≫ q)
    (hh : ∀ (n : ℕ) (i : Fin (n + 1)),
      p.app (op (SimplexCategory.mk n)) ≫ H'.h i =
        H.h i ≫ q.app (op (SimplexCategory.mk (n + 1)))) :
    (p ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫ H'.toSSetHomotopyMap =
      H.toSSetHomotopyMap ≫ q := by
  apply NatTrans.ext
  funext e
  induction e using Opposite.rec with
  | _ e =>
    induction e using SimplexCategory.rec with
    | _ n =>
      apply ConcreteCategory.hom_ext
      intro z
      rcases z with ⟨x, t⟩
      obtain ⟨j, rfl⟩ := SSet.stdSimplex.objMk₁_surjective t
      induction j using Fin.cases with
      | zero =>
        change H'.toSSetHomotopyMap.app (op (SimplexCategory.mk n))
          (p.app (op (SimplexCategory.mk n)) x, SSet.stdSimplex.objMk₁ 0) =
          q.app (op (SimplexCategory.mk n))
            (H.toSSetHomotopyMap.app (op (SimplexCategory.mk n)) (x, SSet.stdSimplex.objMk₁ 0))
        have hLeft := toSSetHomotopyMap_app_objMk₁_zero (X := X') (Y := Y')
          H' n (p.app (op (SimplexCategory.mk n)) x)
        have hRight := toSSetHomotopyMap_app_objMk₁_zero (X := X) (Y := Y) H n x
        have hG := types_congr_hom
          (congrArg (fun t => t.app (op (SimplexCategory.mk n))) hg) x
        change g'.app (op (SimplexCategory.mk n)) (p.app (op (SimplexCategory.mk n)) x) =
          q.app (op (SimplexCategory.mk n)) (g.app (op (SimplexCategory.mk n)) x) at hG
        exact hLeft.trans (hG.trans (congrArg
          (fun y : Y.obj (op (SimplexCategory.mk n)) => q.app (op (SimplexCategory.mk n)) y)
          hRight.symm))
      | succ i =>
        change H'.toSSetHomotopyMap.app (op (SimplexCategory.mk n))
          (p.app (op (SimplexCategory.mk n)) x, SSet.stdSimplex.objMk₁ i.succ) =
          q.app (op (SimplexCategory.mk n))
            (H.toSSetHomotopyMap.app (op (SimplexCategory.mk n)) (x, SSet.stdSimplex.objMk₁ i.succ))
        have h := types_congr_hom (hh n i) x
        have hq := types_congr_hom (q.naturality (SimplexCategory.δ i.succ).op) (H.h i x)
        change H'.h i (p.app (op (SimplexCategory.mk n)) x) =
          q.app (op (SimplexCategory.mk (n + 1))) (H.h i x) at h
        change q.app (op (SimplexCategory.mk n)) (Y.δ i.succ (H.h i x)) =
          Y'.δ i.succ (q.app (op (SimplexCategory.mk (n + 1))) (H.h i x)) at hq
        have hLeft := toSSetHomotopyMap_app_objMk₁_succ (X := X') (Y := Y')
          H' n (p.app (op (SimplexCategory.mk n)) x) i
        have hRight := toSSetHomotopyMap_app_objMk₁_succ (X := X) (Y := Y) H n x i
        exact hLeft.trans
          (((congrArg (fun y : Y'.obj (op (SimplexCategory.mk (n + 1))) => Y'.δ i.succ y)
              h).trans hq.symm).trans
            (congrArg
              (fun y : Y.obj (op (SimplexCategory.mk n)) => q.app (op (SimplexCategory.mk n)) y)
              hRight.symm))

end CategoryTheory.SimplicialObject.Homotopy
