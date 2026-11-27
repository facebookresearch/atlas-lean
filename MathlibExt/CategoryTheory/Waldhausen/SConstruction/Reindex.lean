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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Stage
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs

/-!
# Generic reindexing of finite Waldhausen stages

Turn a simplex-category morphism `f : a ⟶ b` into the covariant indexing
functor `Ar a.len ⥤ Ar b.len` by direct composition of the pinned APIs
`SimplexCategory.Hom.toOrderHom`, `OrderHom.toFunctor`, and
`Functor.mapArrow`. Pointwise inequalities compare these indexing functors
through `Functor.mapArrowFunctor`. Precomposing diagrams then bundles the
result as the contravariant stage functor `Stage C b.len ⟶ Stage C a.len`.

Variance is explicit and strict: no simplicial object, face/degeneracy
wrapper, weak-equivalence category or nerve, realization, Q/S comparison,
or K/G-theory is introduced.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Covariant indexing functor from a simplex map, by direct composition of
the pinned `toOrderHom` / `toFunctor` / `mapArrow` APIs. -/
def indexFunctor {a b : SimplexCategory} (f : a ⟶ b) : Ar a.len ⥤ Ar b.len :=
  (SimplexCategory.Hom.toOrderHom f).toFunctor.mapArrow

/-- A pointwise comparison `alpha i ≤ beta i` induces a natural
transformation between the corresponding indexing functors, oriented from
`alpha` to `beta`. -/
def indexFunctorNatTransOfLE {a b : SimplexCategory}
    (alpha beta : a ⟶ b)
    (h : ∀ i : Fin (a.len + 1),
      SimplexCategory.Hom.toOrderHom alpha i ≤
        SimplexCategory.Hom.toOrderHom beta i) :
    indexFunctor alpha ⟶ indexFunctor beta := by
  let eta :
      (SimplexCategory.Hom.toOrderHom alpha).toFunctor ⟶
        (SimplexCategory.Hom.toOrderHom beta).toFunctor :=
    { app := fun i => homOfLE (h i)
      naturality := fun _ _ _ => Subsingleton.elim _ _ }
  exact (Functor.mapArrowFunctor (Fin (a.len + 1))
    (Fin (b.len + 1))).map eta

/-- The left leg of the component at an interval is the pointwise comparison
at its left endpoint. -/
@[simp]
theorem indexFunctorNatTransOfLE_app_left {a b : SimplexCategory}
    (alpha beta : a ⟶ b)
    (h : ∀ i : Fin (a.len + 1),
      SimplexCategory.Hom.toOrderHom alpha i ≤
        SimplexCategory.Hom.toOrderHom beta i)
    (A : Ar a.len) :
    ((indexFunctorNatTransOfLE alpha beta h).app A).left =
      homOfLE (h A.left) :=
  rfl

/-- The right leg of the component at an interval is the pointwise comparison
at its right endpoint. -/
@[simp]
theorem indexFunctorNatTransOfLE_app_right {a b : SimplexCategory}
    (alpha beta : a ⟶ b)
    (h : ∀ i : Fin (a.len + 1),
      SimplexCategory.Hom.toOrderHom alpha i ≤
        SimplexCategory.Hom.toOrderHom beta i)
    (A : Ar a.len) :
    ((indexFunctorNatTransOfLE alpha beta h).app A).right =
      homOfLE (h A.right) :=
  rfl

/-- A pointwise self-comparison induces the identity transformation of the
corresponding indexing functor, independently of the chosen reflexivity
proofs. -/
theorem indexFunctorNatTransOfLE_self {a b : SimplexCategory}
    (alpha : a ⟶ b)
    (h : ∀ i : Fin (a.len + 1),
      SimplexCategory.Hom.toOrderHom alpha i ≤
        SimplexCategory.Hom.toOrderHom alpha i) :
    indexFunctorNatTransOfLE alpha alpha h = 𝟙 (indexFunctor alpha) := by
  apply NatTrans.ext
  funext A
  apply Arrow.hom_ext <;> exact Subsingleton.elim _ _

/-- Pointwise indexing comparisons commute strictly with precomposition. -/
theorem indexFunctorNatTransOfLE_precomp
    {a' a b : SimplexCategory} (k : a' ⟶ a)
    (alpha beta : a ⟶ b)
    (h : ∀ i : Fin (a.len + 1),
      SimplexCategory.Hom.toOrderHom alpha i ≤
        SimplexCategory.Hom.toOrderHom beta i) :
    indexFunctorNatTransOfLE (k ≫ alpha) (k ≫ beta)
        (fun i => h (SimplexCategory.Hom.toOrderHom k i)) =
      Functor.whiskerLeft (indexFunctor k)
        (indexFunctorNatTransOfLE alpha beta h) := by
  apply NatTrans.ext
  funext A
  apply Arrow.hom_ext <;> exact Subsingleton.elim _ _

/-- Reindexing sends the canonical interval to the mapped interval. -/
@[simp]
theorem indexFunctor_obj_interval {a b : SimplexCategory} (f : a ⟶ b)
    {i j : Fin (a.len + 1)} (h : i ≤ j) :
    (indexFunctor f).obj (interval i j h) =
      interval ((SimplexCategory.Hom.toOrderHom f) i)
        ((SimplexCategory.Hom.toOrderHom f) j)
        ((SimplexCategory.Hom.toOrderHom f).monotone h) := by
  simp only [indexFunctor, interval, Functor.mapArrow_obj, Arrow.mk_hom]
  exact (Arrow.mk_inj _ _).mpr (Subsingleton.elim _ _)

/-- Reindexing sends diagonals to diagonals. -/
@[simp]
theorem indexFunctor_obj_diag {a b : SimplexCategory} (f : a ⟶ b)
    (i : Fin (a.len + 1)) :
    (indexFunctor f).obj (diag i) =
      diag ((SimplexCategory.Hom.toOrderHom f) i) := by
  simp [diag, indexFunctor_obj_interval]

/-- Reindexing sends horizontal maps to horizontal maps. -/
@[simp]
theorem indexFunctor_map_horiz {a b : SimplexCategory} (f : a ⟶ b)
    {i j k : Fin (a.len + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    (indexFunctor f).map (horiz hij hjk) =
      horiz ((SimplexCategory.Hom.toOrderHom f).monotone hij)
        ((SimplexCategory.Hom.toOrderHom f).monotone hjk) := by
  apply Arrow.hom_ext <;> exact Subsingleton.elim _ _

/-- Reindexing sends vertical maps to vertical maps. -/
@[simp]
theorem indexFunctor_map_vert {a b : SimplexCategory} (f : a ⟶ b)
    {i j k : Fin (a.len + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    (indexFunctor f).map (vert hij hjk) =
      vert ((SimplexCategory.Hom.toOrderHom f).monotone hij)
        ((SimplexCategory.Hom.toOrderHom f).monotone hjk) := by
  apply Arrow.hom_ext <;> exact Subsingleton.elim _ _

/-- Contravariant reindexing of bundled stages: a simplex map `a ⟶ b`
gives `Stage C b.len ⟶ Stage C a.len`, via the existing full-subcategory
lift. Precomposition itself is direct `⋙` / `whiskerLeft` reuse; the
`IsStage` proof below reuses the original `diag_isZero` and
`cofiber_triple` after transporting `diag` / `horiz` / `vert` along the
indexing functor. -/
def reindexStage {a b : SimplexCategory} (f : a ⟶ b) :
    Stage C b.len ⥤ Stage C a.len :=
  (stageProperty C a.len).lift
    (forget C b.len ⋙ (Functor.whiskeringLeft _ _ _).obj (indexFunctor f))
    (fun X => by
      change IsStage a.len (indexFunctor f ⋙ X.obj)
      refine { diag_isZero := ?_, cofiber_triple := ?_ }
      · intro i
        have e : (indexFunctor f ⋙ X.obj).obj (diag i) =
            X.obj.obj (diag ((SimplexCategory.Hom.toOrderHom f) i)) := by
          rw [Functor.comp_obj]
          exact congrArg _ (indexFunctor_obj_diag f i)
        rw [e]
        exact X.property.diag_isZero _
      · intro i j k hij hjk
        have e₁ : (indexFunctor f ⋙ X.obj).map (horiz hij hjk) =
            X.obj.map (horiz ((SimplexCategory.Hom.toOrderHom f).monotone hij)
              ((SimplexCategory.Hom.toOrderHom f).monotone hjk)) := by
          rw [Functor.comp_map]
          exact congrArg _ (indexFunctor_map_horiz f hij hjk)
        have e₂ : (indexFunctor f ⋙ X.obj).map (vert hij hjk) =
            X.obj.map (vert ((SimplexCategory.Hom.toOrderHom f).monotone hij)
              ((SimplexCategory.Hom.toOrderHom f).monotone hjk)) := by
          rw [Functor.comp_map]
          exact congrArg _ (indexFunctor_map_vert f hij hjk)
        rw [e₁, e₂]
        exact X.property.cofiber_triple _ _)

/-- Identity simplex map reindexes to the identity stage functor. -/
@[simp]
theorem reindexStage_id (a : SimplexCategory) :
    reindexStage (C := C) (𝟙 a) = 𝟭 (Stage C a.len) := by
  rfl

/-- Composition of simplex maps reindexes contravariantly. -/
@[simp]
theorem reindexStage_comp {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    reindexStage (C := C) (f ≫ g) =
      reindexStage (C := C) g ⋙ reindexStage (C := C) f := by
  rfl

/-- Identity simplex map gives the identity indexing functor. -/
@[simp]
theorem indexFunctor_id (a : SimplexCategory) :
    indexFunctor (𝟙 a) = 𝟭 (Ar a.len) := by
  rfl

/-- Composition of simplex maps gives composed indexing functors. -/
@[simp]
theorem indexFunctor_comp {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    indexFunctor (f ≫ g) = indexFunctor f ⋙ indexFunctor g := by
  rfl

variable (C)

/-- The original pointwise ordinal comparison induces the whole comparison
of the original stage reindex functors. -/
def reindexStageNatTransOfLE {a b : SimplexCategory} (f g : a ⟶ b)
    (h : ∀ i, f.toOrderHom i ≤ g.toOrderHom i) :
    reindexStage (C := C) f ⟶ reindexStage (C := C) g where
  app A := ObjectProperty.homMk
    (Functor.whiskerRight (indexFunctorNatTransOfLE f g h) A.obj)
  naturality A B φ := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext x
    exact (φ.hom.naturality ((indexFunctorNatTransOfLE f g h).app x)).symm

/-- Every original interval component is the original diagram applied to
the same actual ordinal comparison arrow. -/
theorem reindexStageNatTransOfLE_app {a b : SimplexCategory} (f g : a ⟶ b)
    (h : ∀ i, f.toOrderHom i ≤ g.toOrderHom i) (A : Stage C b.len) (x : Ar a.len) :
    ((reindexStageNatTransOfLE C f g h).app A).hom.app x =
      A.obj.map ((indexFunctorNatTransOfLE f g h).app x) := rfl

end CategoryTheory.Waldhausen.SConstruction
