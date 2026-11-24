/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.WeightedBarMapPostcomp

/-
Contract tests for target postcomposition of the strict ordinary weighted
bar: the degreewise inverse laws and the bundled simplicial degree
formulas, plus the total face/degeneracy commutation shapes. All checks are
stated generically over variables with the same hypotheses as the API; no
local instances are introduced.

This tests only the stated interface contract and makes no `SSet`,
`ULift`, Bousfield–Kan, comparison, or homotopy claim.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe uJ vJ uW uC vC uD vD

namespace CategoryTheory.StrictOrdinaryWeightedBar.WeightedBarMapPostcompTests

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {W : Jᵒᵖ ⥤ Type uW} {F : J ⥤ C} (G : C ⥤ D)

example (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G] :
    (wbarObjMapIso (G := G) n).inv =
      Limits.sigmaComparison G (fun p : WIdx J W n => F.obj p.1.left) :=
  wbarObjMapIso_inv_eq (G := G) n

example (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G]
    (p : WIdx J W n) :
    wbarIncl W (F ⋙ G) n p ≫ (wbarObjMapIso (G := G) n).inv =
      G.map (wbarIncl W F n p) :=
  wbarObjMapIso_inv_ι (G := G) n p

example (n : ℕ) (i : Fin (n + 2))
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [∀ n, Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G] :
    (wbarObjMapIso (G := G) (n + 1)).inv ≫ G.map (wbarδ W F n i) =
      wbarδ W (F ⋙ G) n i ≫ (wbarObjMapIso (G := G) n).inv :=
  wbarδ_mapIso_inv (W := W) (F := F) (G := G) n i

example (n : ℕ) (i : Fin (n + 1))
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [∀ n, Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G] :
    (wbarObjMapIso (G := G) n).inv ≫ G.map (wbarσ W F n i) =
      wbarσ W (F ⋙ G) n i ≫ (wbarObjMapIso (G := G) (n + 1)).inv :=
  wbarσ_mapIso_inv (W := W) (F := F) (G := G) n i

example (n : ℕ)
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [∀ n, Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G] :
    (wbarSimplicialMapPostcompIso (W := W) (F := F) (G := G)).hom.app
        (Opposite.op (SimplexCategory.mk n)) =
      (wbarObjMapIso (G := G) n).hom :=
  wbarSimplicialMapPostcompIso_hom_app_mk (W := W) (F := F) (G := G) n

example (n : ℕ)
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [∀ n, Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G] :
    (wbarSimplicialMapPostcompIso (W := W) (F := F) (G := G)).inv.app
        (Opposite.op (SimplexCategory.mk n)) =
      (wbarObjMapIso (G := G) n).inv :=
  wbarSimplicialMapPostcompIso_inv_app_mk (W := W) (F := F) (G := G) n

end CategoryTheory.StrictOrdinaryWeightedBar.WeightedBarMapPostcompTests
