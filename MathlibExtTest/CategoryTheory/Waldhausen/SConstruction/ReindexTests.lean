/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Reindex
import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Zero
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Reindexing consumer tests

Focused public-API checks for generic contravariant reindexing: ordered
comparisons of indexing functors, including a genuine identity-to-last-vertex
crossing; interval and diagonal values with horizontal and vertical maps; the
reindexed zero diagram; and strict identity with contravariant composition.
No simplicial object, nerve, realization, or K/G-theory content.
-/

open CategoryTheory
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.ReindexTests

section IndexFunctorNatTrans

variable {a b : SimplexCategory} (alpha beta : a ⟶ b)
  (h : ∀ i : Fin (a.len + 1),
    SimplexCategory.Hom.toOrderHom alpha i ≤
      SimplexCategory.Hom.toOrderHom beta i)

/-- Pointwise order gives a natural transformation in the increasing
`alpha`-to-`beta` orientation. -/
example : indexFunctor alpha ⟶ indexFunctor beta :=
  indexFunctorNatTransOfLE alpha beta h

/-- The two component legs are the pointwise comparisons at the interval
endpoints. -/
example (A : Ar a.len) :
    ((indexFunctorNatTransOfLE alpha beta h).app A).left =
        homOfLE (h A.left) ∧
      ((indexFunctorNatTransOfLE alpha beta h).app A).right =
        homOfLE (h A.right) :=
  ⟨indexFunctorNatTransOfLE_app_left alpha beta h A,
    indexFunctorNatTransOfLE_app_right alpha beta h A⟩

/-- An arbitrary family of pointwise reflexivity proofs gives the identity
transformation, not merely identity component legs. -/
example
    (hself : ∀ i : Fin (a.len + 1),
      SimplexCategory.Hom.toOrderHom alpha i ≤
        SimplexCategory.Hom.toOrderHom alpha i) :
    indexFunctorNatTransOfLE alpha alpha hself =
      𝟙 (indexFunctor alpha) :=
  indexFunctorNatTransOfLE_self alpha hself

/-- The induced arrow components satisfy naturality in the standard
functorial orientation. -/
example {A B : Ar a.len} (u : A ⟶ B) :
    (indexFunctor alpha).map u ≫
        (indexFunctorNatTransOfLE alpha beta h).app B =
      (indexFunctorNatTransOfLE alpha beta h).app A ≫
        (indexFunctor beta).map u :=
  (indexFunctorNatTransOfLE alpha beta h).naturality u

/-- Pointwise comparisons commute with precomposition. -/
example {a' : SimplexCategory} (k : a' ⟶ a) :
    indexFunctorNatTransOfLE (k ≫ alpha) (k ≫ beta)
        (fun i => h (SimplexCategory.Hom.toOrderHom k i)) =
      Functor.whiskerLeft (indexFunctor k)
        (indexFunctorNatTransOfLE alpha beta h) :=
  indexFunctorNatTransOfLE_precomp k alpha beta h

/-- For the comparison from the identity of `[1]` to the last-vertex
constant map, the component at `(0, 1)` has the genuine crossing `0 ⟶ 1`
on the left and the identity of `1` on the right. -/
example :
    let alpha : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 1 := 𝟙 _
    let beta : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 1 :=
      SimplexCategory.const (SimplexCategory.mk 1) (SimplexCategory.mk 1) 1
    let h : ∀ i : Fin 2,
        SimplexCategory.Hom.toOrderHom alpha i ≤
          SimplexCategory.Hom.toOrderHom beta i :=
      fun i => Fin.le_last i
    ((indexFunctorNatTransOfLE alpha beta h).app
          (interval (0 : Fin 2) (1 : Fin 2) (Fin.zero_le _))).left =
        homOfLE (Fin.zero_le (1 : Fin 2)) ∧
      ((indexFunctorNatTransOfLE alpha beta h).app
          (interval (0 : Fin 2) (1 : Fin 2) (Fin.zero_le _))).right =
        𝟙 (1 : Fin 2) := by
  dsimp only
  constructor <;> exact Subsingleton.elim _ _

/-- The same identity-to-last-vertex comparison satisfies its Arrow
naturality square on the horizontal map `diag 0 ⟶ interval 0 1`. -/
example :
    let alpha : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 1 := 𝟙 _
    let beta : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 1 :=
      SimplexCategory.const (SimplexCategory.mk 1) (SimplexCategory.mk 1) 1
    let h : ∀ i : Fin 2,
        SimplexCategory.Hom.toOrderHom alpha i ≤
          SimplexCategory.Hom.toOrderHom beta i :=
      fun i => Fin.le_last i
    let u : diag (0 : Fin 2) ⟶
        interval (0 : Fin 2) (1 : Fin 2) (Fin.zero_le _) :=
      horiz (le_refl (0 : Fin 2)) (Fin.zero_le _)
    (indexFunctor alpha).map u ≫
        (indexFunctorNatTransOfLE alpha beta h).app
          (interval (0 : Fin 2) (1 : Fin 2) (Fin.zero_le _)) =
      (indexFunctorNatTransOfLE alpha beta h).app (diag (0 : Fin 2)) ≫
        (indexFunctor beta).map u := by
  dsimp only
  exact (indexFunctorNatTransOfLE (𝟙 (SimplexCategory.mk 1))
    (SimplexCategory.const (SimplexCategory.mk 1) (SimplexCategory.mk 1) 1)
    (fun i => Fin.le_last i)).naturality _

/-- Self-comparison is still the identity on the nondegenerate interval
`(0, 1)`; this complements the genuine crossing comparison above. -/
example :
    let alpha : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 1 := 𝟙 _
    let hself : ∀ i : Fin 2,
        SimplexCategory.Hom.toOrderHom alpha i ≤
          SimplexCategory.Hom.toOrderHom alpha i :=
      fun _ => le_rfl
    let A : Ar 1 := interval (0 : Fin 2) (1 : Fin 2) (Fin.zero_le _)
    (indexFunctorNatTransOfLE alpha alpha hself).app A =
      𝟙 ((indexFunctor alpha).obj A) := by
  dsimp only
  rw [indexFunctorNatTransOfLE_self]
  rfl

end IndexFunctorNatTrans

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Reindexing sends intervals to intervals, diagonals to diagonals, and
horizontal and vertical maps to horizontal and vertical maps. -/
example (a b : SimplexCategory) (f : a ⟶ b)
    {i j k : Fin (a.len + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    (indexFunctor f).obj (interval i j hij) =
        interval ((SimplexCategory.Hom.toOrderHom f) i)
          ((SimplexCategory.Hom.toOrderHom f) j)
          ((SimplexCategory.Hom.toOrderHom f).monotone hij) ∧
      (indexFunctor f).obj (diag i) =
        diag ((SimplexCategory.Hom.toOrderHom f) i) ∧
      (indexFunctor f).map (horiz hij hjk) =
        horiz ((SimplexCategory.Hom.toOrderHom f).monotone hij)
          ((SimplexCategory.Hom.toOrderHom f).monotone hjk) ∧
      (indexFunctor f).map (vert hij hjk) =
        vert ((SimplexCategory.Hom.toOrderHom f).monotone hij)
          ((SimplexCategory.Hom.toOrderHom f).monotone hjk) :=
  ⟨indexFunctor_obj_interval f hij, indexFunctor_obj_diag f i,
    indexFunctor_map_horiz f hij hjk, indexFunctor_map_vert f hij hjk⟩

/-- A reindexed zero diagram equals the zero diagram. -/
noncomputable example (a b : SimplexCategory) (f : a ⟶ b) :
    ((reindexStage (C := C) f).obj
      ⟨zeroDiagram C b.len, isStage_zeroDiagram C b.len⟩).obj =
      zeroDiagram C a.len :=
  rfl

/-- Identity reindexes strictly to identity, and composition reindexes in
contravariant order. -/
example (a b c : SimplexCategory) (f : a ⟶ b) (g : b ⟶ c) :
    reindexStage (C := C) (𝟙 b) = 𝟭 (Stage C b.len) ∧
      reindexStage (C := C) (f ≫ g) =
        reindexStage (C := C) g ⋙ reindexStage (C := C) f :=
  ⟨reindexStage_id (C := C) b, reindexStage_comp (C := C) f g⟩

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.ReindexTests
