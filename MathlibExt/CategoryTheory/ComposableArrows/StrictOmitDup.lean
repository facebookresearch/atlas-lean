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

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Strict omit/duplicate infrastructure for composable-arrow chains

This module provides reusable strict finite omit/duplicate chain infrastructure,
independent of weighted-bar imports, for consumption by simplicial replacement
and later weighted-bar inner files. Omission at a finite position uses
`Fin.succAbove` and duplication uses `Fin.predAbove`, both applied to chains by
`whiskerLeftFunctor` precomposition. Endpoint omission reuses
`δ₀Functor` and `δlastFunctor`; endpoint duplication is the `dupAt 0`
instance. Iterated omit/duplicate composites and post-whiskering are compared
by explicit object-level isomorphisms built from `Functor.associator`, never by
definitional identification.

Reuse: `whiskerLeftFunctor`, `δ₀Functor`, `δlastFunctor`,
`Functor.mapComposableArrows`, `Functor.associator`, `Fin.succAbove`,
`Fin.predAbove`. No local indexing, coproduct,
enriched, or model-category API is introduced.

Exact boundary: this file supplies strict finite functors, object-level comparison
isos, and the two endpoint coherence equalities `dropLast_dupFirst_eq` and
`dupFirst_lastArrow_eq`. Inner faces, the simplicial identities, and
any `SimplicialObject.Data`/`GenRel`/genuine packaging are downstream
(`WeightedBarInner` / `WeightedBarData` / `WeightedBarSimplicial`),
not here, as are enriched copowers and coends, profunctors, and derived
conclusions. The next strict consumer is `Enriched/WeightedBarOuter.lean`.
-/

@[expose] public section

namespace CategoryTheory
namespace StrictOmitDup

universe v u vD uD

variable {C : Type u} [Category.{v} C]
variable {D : Type uD} [Category.{vD} D]

/-- Finite omit index functor: embed `Fin (n + 1)` into `Fin (n + 2)` with a
hole at `p`, via the pinned `Fin.succAbove`. -/
def omitFinFunctor (n : ℕ) (p : Fin (n + 2)) : Fin (n + 1) ⥤ Fin (n + 2) where
  obj := p.succAbove
  map {_ _} hij := homOfLE ((Fin.strictMono_succAbove p).monotone (leOfHom hij))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Finite duplicate index functor: project `Fin (n + 2)` onto `Fin (n + 1)`
collapsing `p`, via the pinned `Fin.predAbove`. -/
def dupFinFunctor (n : ℕ) (p : Fin (n + 1)) : Fin (n + 2) ⥤ Fin (n + 1) where
  obj := p.predAbove
  map {_ _} hij := homOfLE ((Fin.predAbove_right_monotone p) (leOfHom hij))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Computation rule for `omitFinFunctor` on objects. -/
@[simp]
theorem omitFinFunctor_obj (n : ℕ) (p : Fin (n + 2)) (i : Fin (n + 1)) :
    (omitFinFunctor n p).obj i = p.succAbove i := rfl

/-- Computation rule for `dupFinFunctor` on objects. -/
@[simp]
theorem dupFinFunctor_obj (n : ℕ) (p : Fin (n + 1)) (i : Fin (n + 2)) :
    (dupFinFunctor n p).obj i = p.predAbove i := rfl

/-- Omitting `0` shifts every index up by one successor. -/
theorem omitFin_zero_succ (n : ℕ) (i : Fin (n + 1)) :
    (omitFinFunctor n 0).obj i = i.succ :=
  Fin.succAbove_of_le_castSucc 0 i (Fin.zero_le _)

/-- Omitting the last index is the cast-successor embedding. -/
theorem omitFin_last_castSucc (n : ℕ) (i : Fin (n + 1)) :
    (omitFinFunctor n (Fin.last (n + 1))).obj i = i.castSucc :=
  congrFun Fin.succAbove_last i

/-- Duplicating `0` fixes the zeroth index. -/
theorem dupFin_zero_obj (n : ℕ) [NeZero (n + 1)] :
    (dupFinFunctor n 0).obj 0 = 0 :=
  Fin.predAbove_right_zero (i := (0 : Fin (n + 1)))

/-- Duplicating `0` sends each successor back to its predecessor. -/
theorem dupFin_zero_succ (n : ℕ) [NeZero (n + 1)] (i : Fin (n + 1)) :
    (dupFinFunctor n 0).obj i.succ = i :=
  Fin.predAbove_zero_succ

/-- Every duplicate index functor preserves the last index. -/
theorem dupFin_last_obj (n : ℕ) (p : Fin (n + 1)) :
    (dupFinFunctor n p).obj (Fin.last (n + 1)) = Fin.last n :=
  Fin.predAbove_right_last

/-- Functorial omission of a composable-arrow chain at the finite position `p`,
by pinned `whiskerLeftFunctor` precomposition. -/
def omitAt {n : ℕ} (p : Fin (n + 2)) :
    ComposableArrows C (n + 1) ⥤ ComposableArrows C n :=
  ComposableArrows.whiskerLeftFunctor (omitFinFunctor n p)

/-- Functorial duplication of a composable-arrow chain at the finite position
`p`, by pinned `whiskerLeftFunctor` precomposition. -/
def dupAt {n : ℕ} (p : Fin (n + 1)) :
    ComposableArrows C n ⥤ ComposableArrows C (n + 1) :=
  ComposableArrows.whiskerLeftFunctor (dupFinFunctor n p)

/-- Endpoint omission at `0` reuses the pinned `δ₀Functor`. -/
def omitZero {n : ℕ} : ComposableArrows C (n + 1) ⥤ ComposableArrows C n :=
  ComposableArrows.δ₀Functor

/-- Endpoint omission at the last index reuses the pinned `δlastFunctor`. -/
def omitLast {n : ℕ} : ComposableArrows C (n + 1) ⥤ ComposableArrows C n :=
  ComposableArrows.δlastFunctor

/-- Endpoint duplication at `0` is the `dupAt 0` instance. -/
def dupZero {n : ℕ} : ComposableArrows C n ⥤ ComposableArrows C (n + 1) :=
  dupAt (0 : Fin (n + 1))

/-- Unfolding rule for `omitAt` on objects. -/
theorem omitAt_obj {n : ℕ} (p : Fin (n + 2)) (F : ComposableArrows C (n + 1)) :
    (omitAt p).obj F = F.whiskerLeft (omitFinFunctor n p) := rfl

/-- Object computation rule for `omitAt`. -/
@[simp]
theorem omitAt_obj_obj {n : ℕ} (p : Fin (n + 2)) (F : ComposableArrows C (n + 1))
    (i : Fin (n + 1)) :
    ((omitAt p).obj F).obj i = F.obj ((omitFinFunctor n p).obj i) := rfl

/-- Component computation rule for `omitAt` on morphisms. -/
@[simp]
theorem omitAt_map_app {n : ℕ} (p : Fin (n + 2))
    {F G : ComposableArrows C (n + 1)} (φ : F ⟶ G) (i : Fin (n + 1)) :
    ((omitAt p).map φ).app i = φ.app ((omitFinFunctor n p).obj i) := rfl

/-- Left-endpoint object computation rule for `omitAt`. -/
@[simp]
theorem omitAt_left {n : ℕ} (p : Fin (n + 2)) (F : ComposableArrows C (n + 1)) :
    ((omitAt p).obj F).obj 0 = F.obj ((omitFinFunctor n p).obj 0) := rfl

/-- Right-endpoint object computation rule for `omitAt`. -/
@[simp]
theorem omitAt_right {n : ℕ} (p : Fin (n + 2)) (F : ComposableArrows C (n + 1)) :
    ((omitAt p).obj F).obj (Fin.last n) =
      F.obj ((omitFinFunctor n p).obj (Fin.last n)) := rfl

/-- Unfolding rule for `dupAt` on objects. -/
theorem dupAt_obj {n : ℕ} (p : Fin (n + 1)) (F : ComposableArrows C n) :
    (dupAt p).obj F = F.whiskerLeft (dupFinFunctor n p) := rfl

/-- Object computation rule for `dupAt`. -/
@[simp]
theorem dupAt_obj_obj {n : ℕ} (p : Fin (n + 1)) (F : ComposableArrows C n)
    (i : Fin (n + 2)) :
    ((dupAt p).obj F).obj i = F.obj ((dupFinFunctor n p).obj i) := rfl

/-- Component computation rule for `dupAt` on morphisms. -/
@[simp]
theorem dupAt_map_app {n : ℕ} (p : Fin (n + 1))
    {F G : ComposableArrows C n} (φ : F ⟶ G) (i : Fin (n + 2)) :
    ((dupAt p).map φ).app i = φ.app ((dupFinFunctor n p).obj i) := rfl

/-- Left-endpoint object computation rule for `dupAt`. -/
@[simp]
theorem dupAt_left {n : ℕ} (p : Fin (n + 1)) (F : ComposableArrows C n) :
    ((dupAt p).obj F).obj 0 = F.obj ((dupFinFunctor n p).obj 0) := rfl

/-- Right-endpoint object computation rule for `dupAt`. -/
@[simp]
theorem dupAt_right {n : ℕ} (p : Fin (n + 1)) (F : ComposableArrows C n) :
    ((dupAt p).obj F).obj (Fin.last (n + 1)) =
      F.obj ((dupFinFunctor n p).obj (Fin.last (n + 1))) := rfl

/-- Dropping the first entry exposes the second entry. -/
theorem omitZero_left {n : ℕ} (F : ComposableArrows C (n + 1)) :
    (omitZero.obj F).left = F.obj' 1 := rfl

/-- Dropping the first entry preserves the right endpoint. -/
theorem omitZero_right {n : ℕ} (F : ComposableArrows C (n + 1)) :
    (omitZero.obj F).right = F.right := rfl

/-- Dropping the last entry preserves the left endpoint. -/
theorem omitLast_left {n : ℕ} (F : ComposableArrows C (n + 1)) :
    (omitLast.obj F).left = F.left := rfl

/-- Dropping the last entry exposes the second-to-last vertex. -/
theorem omitLast_right {n : ℕ} (F : ComposableArrows C (n + 1)) :
    (omitLast.obj F).right = F.obj' n := rfl

/-- Endpoint duplication at `0` fixes the zeroth object. -/
theorem dupZero_obj_zero {n : ℕ} [NeZero (n + 1)] (F : ComposableArrows C n) :
    ((dupZero).obj F).obj 0 = F.obj 0 :=
  congrArg F.obj (dupFin_zero_obj n)

/-- Endpoint duplication preserves the right endpoint object. -/
theorem dupAt_obj_last {n : ℕ} (p : Fin (n + 1)) (F : ComposableArrows C n) :
    ((dupAt p).obj F).obj (Fin.last (n + 1)) = F.obj (Fin.last n) :=
  congrArg F.obj (dupFin_last_obj n p)

/-- Transport along an index equality inside an omitted chain. -/
def omitAt_objEqToHom {n : ℕ} (p : Fin (n + 2)) (F : ComposableArrows C (n + 1))
    {a b : Fin (n + 1)} (h : a = b) :
    ((omitAt p).obj F).obj a ⟶ ((omitAt p).obj F).obj b :=
  eqToHom (congrArg (((omitAt p).obj F).obj) h)

/-- Transport along an index equality inside a duplicated chain. -/
def dupAt_objEqToHom {n : ℕ} (p : Fin (n + 1)) (F : ComposableArrows C n)
    {a b : Fin (n + 2)} (h : a = b) :
    ((dupAt p).obj F).obj a ⟶ ((dupAt p).obj F).obj b :=
  eqToHom (congrArg (((dupAt p).obj F).obj) h)

/-- Iterated omission compared by the functor associator, never by a
definitional identification. -/
def omitOmitObjIso {n : ℕ} (p : Fin (n + 3)) (q : Fin (n + 2))
    (F : ComposableArrows C (n + 2)) :
    (ComposableArrows.whiskerLeftFunctor
      ((omitFinFunctor n q) ⋙ (omitFinFunctor (n + 1) p))).obj F ≅
      (omitAt q).obj ((omitAt p).obj F) :=
  Functor.associator _ _ _

/-- Iterated duplication compared by the functor associator, never by a
definitional identification. -/
def dupDupObjIso {n : ℕ} (p : Fin (n + 1)) (q : Fin (n + 2))
    (F : ComposableArrows C n) :
    (ComposableArrows.whiskerLeftFunctor
      ((dupFinFunctor (n + 1) q) ⋙ (dupFinFunctor n p))).obj F ≅
      (dupAt q).obj ((dupAt p).obj F) :=
  Functor.associator _ _ _

/-- Duplicate-then-omit compared by the functor associator, never by a
definitional identification. -/
def omitDupObjIso {n : ℕ} (p : Fin (n + 1)) (q : Fin (n + 2))
    (F : ComposableArrows C n) :
    (ComposableArrows.whiskerLeftFunctor
      ((omitFinFunctor n q) ⋙ (dupFinFunctor n p))).obj F ≅
      (omitAt q).obj ((dupAt p).obj F) :=
  Functor.associator _ _ _

/-- Post-whiskering commutes with pre-whiskering up to the functor associator,
never by a definitional identification. -/
def mapWhiskerObjIso {n m : ℕ} (Φ : Fin (n + 1) ⥤ Fin (m + 1))
    (F : ComposableArrows C m) (G : C ⥤ D) :
    (G.mapComposableArrows n).obj (F.whiskerLeft Φ) ≅
      ((G.mapComposableArrows m).obj F).whiskerLeft Φ :=
  Functor.associator _ _ _

/-- Forward component of `omitOmitObjIso` is the identity. -/
@[simp]
theorem omitOmitObjIso_hom_app {n : ℕ} (p : Fin (n + 3)) (q : Fin (n + 2))
    (F : ComposableArrows C (n + 2)) (i : Fin (n + 1)) :
    (omitOmitObjIso p q F).hom.app i = 𝟙 _ := rfl

/-- Inverse component of `omitOmitObjIso` is the identity. -/
@[simp]
theorem omitOmitObjIso_inv_app {n : ℕ} (p : Fin (n + 3)) (q : Fin (n + 2))
    (F : ComposableArrows C (n + 2)) (i : Fin (n + 1)) :
    (omitOmitObjIso p q F).inv.app i = 𝟙 _ := rfl

/-- Forward component of `dupDupObjIso` is the identity. -/
@[simp]
theorem dupDupObjIso_hom_app {n : ℕ} (p : Fin (n + 1)) (q : Fin (n + 2))
    (F : ComposableArrows C n) (i : Fin (n + 3)) :
    (dupDupObjIso p q F).hom.app i = 𝟙 _ := rfl

/-- Inverse component of `dupDupObjIso` is the identity. -/
@[simp]
theorem dupDupObjIso_inv_app {n : ℕ} (p : Fin (n + 1)) (q : Fin (n + 2))
    (F : ComposableArrows C n) (i : Fin (n + 3)) :
    (dupDupObjIso p q F).inv.app i = 𝟙 _ := rfl

/-- Forward component of `omitDupObjIso` is the identity. -/
@[simp]
theorem omitDupObjIso_hom_app {n : ℕ} (p : Fin (n + 1)) (q : Fin (n + 2))
    (F : ComposableArrows C n) (i : Fin (n + 1)) :
    (omitDupObjIso p q F).hom.app i = 𝟙 _ := rfl

/-- Inverse component of `omitDupObjIso` is the identity. -/
@[simp]
theorem omitDupObjIso_inv_app {n : ℕ} (p : Fin (n + 1)) (q : Fin (n + 2))
    (F : ComposableArrows C n) (i : Fin (n + 1)) :
    (omitDupObjIso p q F).inv.app i = 𝟙 _ := rfl

/-- Forward component of `mapWhiskerObjIso` is the identity. -/
@[simp]
theorem mapWhiskerObjIso_hom_app {n m : ℕ} (Φ : Fin (n + 1) ⥤ Fin (m + 1))
    (F : ComposableArrows C m) (G : C ⥤ D) (i : Fin (n + 1)) :
    (mapWhiskerObjIso Φ F G).hom.app i = 𝟙 _ := rfl

/-- Inverse component of `mapWhiskerObjIso` is the identity. -/
@[simp]
theorem mapWhiskerObjIso_inv_app {n m : ℕ} (Φ : Fin (n + 1) ⥤ Fin (m + 1))
    (F : ComposableArrows C m) (G : C ⥤ D) (i : Fin (n + 1)) :
    (mapWhiskerObjIso Φ F G).inv.app i = 𝟙 _ := rfl

/-- Drop-last after duplicating the first object equals duplicating the first
object after drop-last, with pinned endpoints. -/
theorem dropLast_dupFirst_eq {n : ℕ} (s : ComposableArrows C (n + 1)) :
    ComposableArrows.δlastFunctor.obj (s.precomp (𝟙 s.left)) =
      (ComposableArrows.δlastFunctor.obj s).precomp (𝟙 _) := by
  refine Functor.ext (fun i => ?_) (fun X Y f => ?_)
  · dsimp only [ComposableArrows.δlastFunctor, Fin.castSuccFunctor,
      ComposableArrows.whiskerLeftFunctor, ComposableArrows.whiskerLeft,
      ComposableArrows.precomp]
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero => rfl
    | succ k => rfl
  · dsimp only [ComposableArrows.δlastFunctor, Fin.castSuccFunctor,
      ComposableArrows.whiskerLeftFunctor, ComposableArrows.whiskerLeft,
      ComposableArrows.precomp]
    obtain ⟨a, ha⟩ := X
    obtain ⟨b, hb⟩ := Y
    cases a with
    | zero =>
      cases b with
      | zero =>
        rw [Functor.comp_map]
        change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
        simp
      | succ b =>
        cases b with
        | zero =>
          rw [Functor.comp_map]
          change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
          simp
        | succ c =>
          rw [Functor.comp_map]
          change _ = 𝟙 _ ≫ (𝟙 _ ≫ _) ≫ 𝟙 _
          simp only [Category.id_comp, Category.comp_id]
          simp only [Fin.zero_eta, Fin.castSucc_zero, ComposableArrows.Precomp.obj_zero,
            Fin.castSucc_mk, ComposableArrows.Precomp.obj_succ, ComposableArrows.obj',
            ComposableArrows.Precomp.map_zero_succ_succ, ComposableArrows.map',
            homOfLE_leOfHom, Functor.comp_map]
          exact Category.id_comp _
    | succ a =>
      cases b with
      | zero =>
        have hle : a + 1 ≤ 0 := by simpa using leOfHom f
        exact absurd hle (by omega)
      | succ b =>
        rw [Functor.comp_map]
        change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
        simp [Fin.castSucc, ComposableArrows.Precomp.map]
        rfl

/-- Duplicating the first object preserves the original last arrow. -/
theorem dupFirst_lastArrow_eq {n : ℕ} (s : ComposableArrows C (n + 1)) :
    (s.precomp (𝟙 s.left)).map' (n + 1) (n + 1 + 1) = s.map' n (n + 1) := by
  simp [ComposableArrows.map', ComposableArrows.precomp]

end StrictOmitDup
end CategoryTheory
