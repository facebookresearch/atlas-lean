/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplexCategory.AbsoluteCofacePullbacks

/-! # Original Type-valued coface-square clients -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v

open CategoryTheory Limits SimplexCategory
open scoped Simplicial

namespace AbsoluteCofacePullbacksTest

/-- A client keeps both actual projection equations of an arbitrary source map. -/
theorem wholeMapFiller (H : SimplexCategory ⥤ Type v) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 3)) (h : i.castSucc < j)
    (A : Type v) (a b : A ⟶ H.obj ⦋n + 1⦌)
    (w : a ≫ H.map (δ i.castSucc) = b ≫ H.map (δ j)) :
    ∃! t : A ⟶ H.obj ⦋n⦌,
      t ≫ H.map (δ (j.pred h.ne_zero)) = a ∧ t ≫ H.map (δ i) = b := by
  let hp := absoluteCofacePullback H i j h
  refine ⟨hp.lift a b w, ⟨hp.lift_fst a b w, hp.lift_snd a b w⟩, ?_⟩
  intro t ht
  apply hp.hom_ext
  · exact ht.1.trans (hp.lift_fst a b w).symm
  · exact ht.2.trans (hp.lift_snd a b w).symm

/-- Both lift equations determine its behavior under every original precomposition. -/
theorem wholeMapFiller_precomp (H : SimplexCategory ⥤ Type v) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 3)) (h : i.castSucc < j)
    {A A' : Type v} (r : A' ⟶ A) (a b : A ⟶ H.obj ⦋n + 1⦌)
    (w : a ≫ H.map (δ i.castSucc) = b ≫ H.map (δ j)) :
    (absoluteCofacePullback H i j h).lift (r ≫ a) (r ≫ b)
      (by simpa only [Category.assoc] using congrArg (r ≫ ·) w) =
      r ≫ (absoluteCofacePullback H i j h).lift a b w := by
  apply (absoluteCofacePullback H i j h).hom_ext <;> simp

/-- The first smallest corner removes the two initial target vertices. -/
theorem initialPair (H : SimplexCategory ⥤ Type v) :
    IsPullback (H.map (δ (0 : Fin 2))) (H.map (δ (0 : Fin 2)))
      (H.map (δ (0 : Fin 3))) (H.map (δ (1 : Fin 3))) :=
  absoluteCofacePullback H (0 : Fin 2) (1 : Fin 3) (by decide)

/-- The second smallest corner retains the original middle target vertex. -/
theorem endpointPair (H : SimplexCategory ⥤ Type v) :
    IsPullback (H.map (δ (1 : Fin 2))) (H.map (δ (0 : Fin 2)))
      (H.map (δ (0 : Fin 3))) (H.map (δ (2 : Fin 3))) :=
  absoluteCofacePullback H (0 : Fin 2) (2 : Fin 3) (by decide)

/-- The third smallest corner removes the two final target vertices. -/
theorem finalPair (H : SimplexCategory ⥤ Type v) :
    IsPullback (H.map (δ (1 : Fin 2))) (H.map (δ (1 : Fin 2)))
      (H.map (δ (1 : Fin 3))) (H.map (δ (2 : Fin 3))) :=
  absoluteCofacePullback H (1 : Fin 2) (2 : Fin 3) (by decide)

end AbsoluteCofacePullbacksTest
