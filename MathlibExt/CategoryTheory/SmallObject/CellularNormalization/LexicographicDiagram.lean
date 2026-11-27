/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.Order.Sigma
public import Mathlib.Order.RelClasses

/-!
# Original variable lexicographic diagrams and endpoint cocones

Retain the actual inner objects, transitions, bottom maps and endpoint legs.
The whole endpoint universal property is constructed in LexicographicEndpoint.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w w'

namespace CategoryTheory.SmallObject.CellularNormalization

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [LinearOrder J] [SuccOrder J]
variable {K : J → Type w'} [∀ j, LinearOrder (K j)] [∀ j, SuccOrder (K j)]
  [∀ j, OrderBot (K j)] [∀ j, WellFoundedLT (K j)]
variable (F : J ⥤ C)
variable (c : ∀ j, TransfiniteCompositionOfShape (K j)
  (F.map (homOfLE (Order.le_succ j))))

/-- The dependent lexicographic sum of the original inner orders. -/
abbrev Index (K : J → Type w') := Lex (Sigma K)

/-- An original inner vertex viewed in the dependent lexicographic sum. -/
abbrev vertex (j : J) (k : K j) : Index K := toLex ⟨j, k⟩

/-- The actual root-to-stage map of an original inner presentation. -/
def innerRoot (j : J) (k : K j) : F.obj j ⟶ (c j).F.obj k :=
  (c j).isoBot.inv ≫ (c j).F.map (homOfLE bot_le)

@[reassoc]
theorem innerRoot_naturality (j : J) {k k' : K j} (h : k ≤ k') :
    innerRoot F c j k ≫ (c j).F.map (homOfLE h) = innerRoot F c j k' := by
  dsimp [innerRoot]
  rw [Category.assoc, ← Functor.map_comp]
  rfl

@[reassoc]
theorem innerRoot_endpoint (j : J) (k : K j) :
    innerRoot F c j k ≫ (c j).incl.app k =
      F.map (homOfLE (Order.le_succ j)) := by
  dsimp [innerRoot]
  rw [Category.assoc]
  rw [NatTrans.naturality]
  simp

/-- Crossing blocks uses the original endpoint cocone and original outer map. -/
def crossMap {i j : J} (h : i < j) (k : K i) (l : K j) :
    (c i).F.obj k ⟶ (c j).F.obj l :=
  (c i).incl.app k ≫ F.map (homOfLE (Order.succ_le_of_lt h)) ≫ innerRoot F c j l

@[reassoc]
theorem inner_then_cross {i j : J} (h : i < j) {k k' : K i} (hk : k ≤ k')
    (l : K j) :
    (c i).F.map (homOfLE hk) ≫ crossMap F c h k' l = crossMap F c h k l := by
  dsimp [crossMap]
  rw [← Category.assoc, NatTrans.naturality]
  simp

@[reassoc]
theorem cross_then_inner {i j : J} (h : i < j) (k : K i) {l l' : K j}
    (hl : l ≤ l') :
    crossMap F c h k l ≫ (c j).F.map (homOfLE hl) = crossMap F c h k l' := by
  dsimp [crossMap]
  simp only [Category.assoc, innerRoot_naturality]

@[reassoc]
theorem cross_then_cross {i j m : J} (hij : i < j) (hjm : j < m)
    (k : K i) (l : K j) (n : K m) :
    crossMap F c hij k l ≫ crossMap F c hjm l n =
      crossMap F c (hij.trans hjm) k n := by
  dsimp [crossMap]
  simp only [Category.assoc, innerRoot_endpoint_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  rfl

/-- The lexicographic map retains inner maps and all original outer transitions. -/
def sigmaMap (a b : Sigma K) (h : Sigma.Lex (· < ·) (fun _ => (· ≤ ·)) a b) :
    (c a.1).F.obj a.2 ⟶ (c b.1).F.obj b.2 := by
  classical
  rcases a with ⟨i, k⟩
  rcases b with ⟨j, l⟩
  by_cases e : i = j
  · subst j
    exact (c i).F.map (homOfLE
      ((Sigma.lex_iff.mp h).resolve_left (lt_irrefl i)).choose_spec)
  · exact crossMap F c
      ((Sigma.lex_iff.mp h).resolve_right (fun he => e he.choose)) k l

/-- The original inner or crossing morphism corresponding to a flat inequality. -/
def indexMap (a b : Index K) (h : a ≤ b) :
    (c (ofLex a).1).F.obj (ofLex a).2 ⟶ (c (ofLex b).1).F.obj (ofLex b).2 :=
  sigmaMap F c (ofLex a) (ofLex b) h

@[simp]
theorem indexMap_inner (j : J) {k l : K j} (h : k ≤ l) :
    indexMap F c (vertex j k) (vertex j l) (Sigma.Lex.right k l h) =
      (c j).F.map (homOfLE h) := by
  change sigmaMap F c ⟨j, k⟩ ⟨j, l⟩ _ = _
  simp [sigmaMap]

@[simp]
theorem indexMap_cross {i j : J} (h : i < j) (k : K i) (l : K j) :
    indexMap F c (vertex i k) (vertex j l) (Sigma.Lex.left k l h) =
      crossMap F c h k l := by
  change sigmaMap F c ⟨i, k⟩ ⟨j, l⟩ _ = _
  simp [sigmaMap, h.ne]

/-- The flattened diagram has exactly the original inner vertices. -/
def diagram : Index K ⥤ C where
  obj a := (c (ofLex a).1).F.obj (ofLex a).2
  map f := indexMap F c _ _ (leOfHom f)
  map_id a := by
    rcases a with ⟨j, k⟩
    change indexMap F c (vertex j k) (vertex j k) _ = 𝟙 _
    rw [indexMap_inner]
    exact (c j).F.map_id k
  map_comp {a b d} f g := by
    rcases a with ⟨i, k⟩
    rcases b with ⟨j, l⟩
    rcases d with ⟨m, n⟩
    have hf := leOfHom f
    have hg := leOfHom g
    cases hf with
    | left k l hij =>
      cases hg with
      | left l n hjm =>
        change indexMap F c (vertex i k) (vertex m n) _ =
          indexMap F c (vertex i k) (vertex j l) _ ≫ indexMap F c (vertex j l) (vertex m n) _
        rw [indexMap_cross F c (hij.trans hjm), indexMap_cross F c hij, indexMap_cross F c hjm]
        exact (cross_then_cross F c hij hjm k l n).symm
      | right l n hln =>
        change indexMap F c (vertex i k) (vertex j n) _ =
          indexMap F c (vertex i k) (vertex j l) _ ≫ indexMap F c (vertex j l) (vertex j n) _
        rw [indexMap_cross F c hij, indexMap_cross F c hij, indexMap_inner]
        exact (cross_then_inner F c hij k hln).symm
    | right k l hkl =>
      cases hg with
      | left l n hjm =>
        change indexMap F c (vertex i k) (vertex m n) _ =
          indexMap F c (vertex i k) (vertex i l) _ ≫ indexMap F c (vertex i l) (vertex m n) _
        rw [indexMap_cross F c hjm, indexMap_inner, indexMap_cross F c hjm]
        exact (inner_then_cross F c hjm hkl n).symm
      | right l n hln =>
        change indexMap F c (vertex i k) (vertex i n) _ =
          indexMap F c (vertex i k) (vertex i l) _ ≫ indexMap F c (vertex i l) (vertex i n) _
        rw [indexMap_inner, indexMap_inner, indexMap_inner]
        exact (c i).F.map_comp (homOfLE hkl) (homOfLE hln)

@[simp]
theorem diagram_obj (j : J) (k : K j) :
    (diagram F c).obj (vertex j k) = (c j).F.obj k := rfl

@[simp]
theorem diagram_inner_map (j : J) {k l : K j} (h : k ≤ l) :
    (diagram F c).map (homOfLE (show vertex j k ≤ vertex j l from Sigma.Lex.right k l h)) =
      (c j).F.map (homOfLE h) := indexMap_inner F c j h

@[simp]
theorem diagram_cross_map {i j : J} (h : i < j) (k : K i) (l : K j) :
    (diagram F c).map (homOfLE (show vertex i k ≤ vertex j l from Sigma.Lex.left k l h)) =
      crossMap F c h k l := indexMap_cross F c h k l

/-- The root of a later block composed with a crossing map is the original outer map. -/
@[reassoc]
theorem root_then_cross {i j : J} (h : i < j) (k : K i) (l : K j) :
    innerRoot F c i k ≫ crossMap F c h k l =
      F.map (homOfLE h.le) ≫ innerRoot F c j l := by
  dsimp [crossMap]
  simp only [← Category.assoc, innerRoot_endpoint]
  rw [← Functor.map_comp]
  rfl


/-- Each original block is a literal restriction of the flattened diagram. -/
def blockInclusion (j : J) : K j ⥤ Index K :=
  { obj k := vertex j k
    map f := homOfLE (Sigma.Lex.right _ _ (leOfHom f)) }

@[simp]
theorem block_restriction (j : J) : blockInclusion (K := K) j ⋙ diagram F c = (c j).F := by
  refine Functor.ext (fun k => rfl) (fun k l f => ?_)
  change indexMap F c (vertex j k) (vertex j l) (Sigma.Lex.right k l (leOfHom f)) =
    (𝟙 _) ≫ (c j).F.map f ≫ 𝟙 _
  exact (indexMap_inner F c j (leOfHom f)).trans
    ((congrArg (c j).F.map (Subsingleton.elim (homOfLE (leOfHom f)) f)).trans
      ((Category.id_comp _).symm.trans
        (congrArg (fun t => (𝟙 _) ≫ t) (Category.comp_id _).symm)))

variable {Y : C} (ι : F ⟶ (Functor.const J).obj Y)

/-- The flattened endpoint uses exactly the original inner and outer colimit legs. -/
def endpoint : diagram F c ⟶ (Functor.const _).obj Y where
  app a := (c (ofLex a).1).incl.app (ofLex a).2 ≫ ι.app (Order.succ (ofLex a).1)
  naturality {a b} f := by
    rcases a with ⟨i, k⟩
    rcases b with ⟨j, l⟩
    have hf := leOfHom f
    obtain rfl : f = homOfLE hf := (homOfLE_leOfHom f).symm
    cases hf with
    | left k l hij =>
      change indexMap F c (vertex i k) (vertex j l) _ ≫
        ((c j).incl.app l ≫ ι.app (Order.succ j)) =
        ((c i).incl.app k ≫ ι.app (Order.succ i)) ≫ 𝟙 Y
      rw [indexMap_cross F c hij]
      change crossMap F c hij k l ≫ ((c j).incl.app l ≫ ι.app (Order.succ j)) =
        ((c i).incl.app k ≫ ι.app (Order.succ i)) ≫ 𝟙 Y
      dsimp [crossMap]
      simp only [Category.assoc, innerRoot_endpoint_assoc]
      rw [← Functor.map_comp_assoc, NatTrans.naturality]
      simp
    | right k l hkl =>
      change indexMap F c (vertex i k) (vertex i l) (Sigma.Lex.right k l hkl) ≫
        ((c i).incl.app l ≫ ι.app (Order.succ i)) =
        ((c i).incl.app k ≫ ι.app (Order.succ i)) ≫ 𝟙 Y
      rw [indexMap_inner]
      change (c i).F.map (homOfLE hkl) ≫
        ((c i).incl.app l ≫ ι.app (Order.succ i)) =
        ((c i).incl.app k ≫ ι.app (Order.succ i)) ≫ 𝟙 Y
      rw [← Category.assoc, NatTrans.naturality]
      simp

@[reassoc]
theorem innerRoot_endpoint_leg (j : J) (k : K j) :
    innerRoot F c j k ≫ (endpoint F c ι).app (vertex j k) = ι.app j := by
  change innerRoot F c j k ≫ ((c j).incl.app k ≫ ι.app (Order.succ j)) = ι.app j
  rw [← Category.assoc, innerRoot_endpoint, NatTrans.naturality]
  simp

end CategoryTheory.SmallObject.CellularNormalization
