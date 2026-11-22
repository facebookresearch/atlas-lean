/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialObjectHomotopyDiagonalEndpoints

/-!
# Fixed original sections of diagonal combinatorial homotopies

A whole original section is fixed by the actual diagonal interval map
when every original homotopy face restricts to its matching next-degree
section. The result keeps the entire section and every interval simplex.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject.Homotopy

/-- Whole original homotopy-face fixedness gives the actual diagonal interval fixed-section equation. -/
theorem diagonalHomotopyMap_fixed_section {X : SimplicialObject SSet.{u}}
    {f g : X ⟶ X} (H : SimplicialObject.Homotopy f g)
    (s : (SimplicialObject.const SSet.{u}).obj (Δ[0] : SSet.{u}) ⟶ X)
    (hs : s ≫ g = s)
    (hh : ∀ (n : ℕ) (i : Fin (n + 1)),
      s.app (op (SimplexCategory.mk n)) ≫ H.h i = s.app (op (SimplexCategory.mk (n + 1)))) :
    (SSet.simplicialDiagonalFunctor.map s ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫ diagonalHomotopyMap H =
      CartesianMonoidalCategory.fst
        (SSet.simplicialDiagonalFunctor.obj ((SimplicialObject.const SSet.{u}).obj (Δ[0] : SSet.{u})))
        (Δ[1] : SSet.{u}) ≫ SSet.simplicialDiagonalFunctor.map s := by
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
        let x₀ : (Δ[0] : SSet.{u}).obj (op (SimplexCategory.mk n)) := x
        change (innerEvaluation H (op (SimplexCategory.mk n))).toSSetHomotopyMap.app
            (op (SimplexCategory.mk n)) ((s.app (op (SimplexCategory.mk n))).app
              (op (SimplexCategory.mk n)) x₀, SSet.stdSimplex.objMk₁ 0) =
          (s.app (op (SimplexCategory.mk n))).app (op (SimplexCategory.mk n)) x₀
        have hEval := toSSetHomotopyMap_app_objMk₁_zero
          (innerEvaluation H (op (SimplexCategory.mk n))) n
          ((s.app (op (SimplexCategory.mk n))).app (op (SimplexCategory.mk n)) x₀)
        exact hEval.trans (types_congr_hom
          (congrArg (fun q => q.app (op (SimplexCategory.mk n)))
            (congrArg (fun q => q.app (op (SimplexCategory.mk n))) hs)) x₀)
      | succ i =>
        let x₀ : (Δ[0] : SSet.{u}).obj (op (SimplexCategory.mk n)) := x
        change (innerEvaluation H (op (SimplexCategory.mk n))).toSSetHomotopyMap.app
            (op (SimplexCategory.mk n)) ((s.app (op (SimplexCategory.mk n))).app
              (op (SimplexCategory.mk n)) x₀, SSet.stdSimplex.objMk₁ i.succ) =
          (s.app (op (SimplexCategory.mk n))).app (op (SimplexCategory.mk n)) x₀
        have hEval := toSSetHomotopyMap_app_objMk₁_succ
          (innerEvaluation H (op (SimplexCategory.mk n))) n
          ((s.app (op (SimplexCategory.mk n))).app (op (SimplexCategory.mk n)) x₀) i
        have hi := types_congr_hom (congrArg (fun q => q.app (op (SimplexCategory.mk n))) (hh n i)) x₀
        have hn := types_congr_hom
          (congrArg (fun q => q.app (op (SimplexCategory.mk n)))
            (s.naturality (SimplexCategory.δ i.succ).op)) x₀
        exact hEval.trans ((congrArg
          (fun v : (X.obj (op (SimplexCategory.mk (n + 1)))).obj (op (SimplexCategory.mk n)) =>
            ((X.map (SimplexCategory.δ i.succ).op).app (op (SimplexCategory.mk n))) v)
          hi).trans hn.symm)

end CategoryTheory.SimplicialObject.Homotopy
