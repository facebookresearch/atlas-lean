/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.WithTerminal.Basic
public import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Tactic.FinCases
import MathlibExt.CategoryTheory.NerveCrossUniverse

/-!
# Canonical cospan and coherent-square indexing shapes

The cospan is the universe-lifted standard walking cospan. Adjoining its
initial object gives the complete diamond, with both triangles and their
common diagonal. The cospan inclusion is the native WithInitial inclusion.
The first walking-cospan branch is the right branch of the drawn square.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet.NativePullback

/-- The standard walking cospan at the simplicial value universe. -/
abbrev CospanObjects := ULift.{u} WalkingCospan

/-- The native lifted category structure, definitionally the standard ULift category. -/
instance cospanCategory : Category.{0} CospanObjects.{u} :=
  CategoryTheory.uliftCategory WalkingCospan

/-- The coherent diamond is the walking cospan with an initial object adjoined. -/
abbrev DiamondObjects := WithInitial CospanObjects.{u}

instance cospanIsThin : Quiver.IsThin CospanObjects.{u} := fun x y => by
  change Subsingleton (x.down ⟶ y.down)
  infer_instance

instance diamondIsThin : Quiver.IsThin DiamondObjects.{u} := fun x y => by
  cases x with
  | star =>
    cases y <;> change Subsingleton PUnit <;> infer_instance
  | of x =>
    cases y with
    | star => change Subsingleton PEmpty; infer_instance
    | of y => change Subsingleton (x ⟶ y); exact cospanIsThin x y

/-- The canonical inclusion of the walking cospan into its initial-object completion. -/
abbrev cospanInclusionFunctor : CospanObjects.{u} ⥤ DiamondObjects.{u} := WithInitial.incl

/-- The full ordinary nerve of the coherent diamond. -/
abbrev squareShape : SSet.{u} := nerve DiamondObjects.{u}

/-- The full ordinary nerve of the standard walking cospan. -/
abbrev cospanShape : SSet.{u} := nerve CospanObjects.{u}

/-- The full nerve map of the standard WithInitial inclusion. -/
def cospanInclusion : cospanShape.{u} ⟶ squareShape.{u} :=
  nerveMap cospanInclusionFunctor

/-- A vertex of the canonical coherent square. -/
def point (v : DiamondObjects.{u}) : (Δ[0] : SSet.{u}) ⟶ squareShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₀ v)

/-- A native arrow of the canonical coherent square, with all its degeneracies. -/
def edge {a b : DiamondObjects.{u}} (f : a ⟶ b) :
    (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₁ f)

/-- The top side from the adjoined initial vertex to the first branch. -/
def topEdge : (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  edge (WithInitial.homTo (ULift.up WalkingCospan.left))

/-- The left side from the adjoined initial vertex to the second branch. -/
def leftEdge : (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  edge (WithInitial.homTo (ULift.up WalkingCospan.right))

/-- The right side from the first branch to the common cospan target. -/
def rightEdge : (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  edge (WithInitial.incl.map (show (ULift.up WalkingCospan.left : CospanObjects.{u}) ⟶
    ULift.up WalkingCospan.one from WalkingCospan.Hom.inl))

/-- The bottom side from the second branch to the common cospan target. -/
def bottomEdge : (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  edge (WithInitial.incl.map (show (ULift.up WalkingCospan.right : CospanObjects.{u}) ⟶
    ULift.up WalkingCospan.one from WalkingCospan.Hom.inr))

end SSet.NativePullback

namespace SSet.NativePullback.Coordinate

/- The coordinate preorder is private proof infrastructure. Its whole nerve
is compared with the canonical shapes by genuine categorical equivalences. -/


/-- The four vertices of the original coherent square. -/
private abbrev DiamondObjects := ULift.{u} (Fin 2 × Fin 2)

/-- The original cospan is the full subcategory without the initial vertex. -/
private abbrev CospanObjects := {v : DiamondObjects.{u} // v.down ≠ (0, 0)}

/-- The full-subcategory inclusion retains each original cospan object. -/
private def cospanInclusionFunctor : CospanObjects.{u} ⥤ DiamondObjects.{u} :=
  (show Monotone (Subtype.val : CospanObjects.{u} → DiamondObjects.{u})
    from fun _ _ h => h).functor

/-- The whole original square shape. -/
private abbrev squareShape : SSet.{u} := nerve DiamondObjects.{u}

/-- The whole original cospan shape. -/
private abbrev cospanShape : SSet.{u} := nerve CospanObjects.{u}

/-- The actual cospan-to-square map, with all original nerve simplices. -/
private def cospanInclusion : cospanShape.{u} ⟶ squareShape.{u} :=
  nerveMap cospanInclusionFunctor

/-- An original square vertex, as an actual standard zero-simplex map. -/
private def point (v : DiamondObjects.{u}) : (Δ[0] : SSet.{u}) ⟶ squareShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₀ v)

/-- An original square arrow, as an actual standard one-simplex map. -/
private def edge (a b : DiamondObjects.{u}) (h : a ≤ b) :
    (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₁ (homOfLE h))

/-- The upper horizontal side from the initial vertex to the right branch. -/
private def topEdge : (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  edge ⟨(0, 0)⟩ ⟨(1, 0)⟩ ⟨by decide, by decide⟩

/-- The left vertical side from the initial vertex to the left branch. -/
private def leftEdge : (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  edge ⟨(0, 0)⟩ ⟨(0, 1)⟩ ⟨by decide, by decide⟩

/-- The right vertical side from the right branch to the target. -/
private def rightEdge : (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  edge ⟨(1, 0)⟩ ⟨(1, 1)⟩ ⟨by decide, by decide⟩

/-- The lower horizontal side from the left branch to the target. -/
private def bottomEdge : (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  edge ⟨(0, 1)⟩ ⟨(1, 1)⟩ ⟨by decide, by decide⟩


private def squareObjectEquiv : DiamondObjects.{u} ≃ SSet.NativePullback.DiamondObjects.{u} where
  toFun v :=
    if v.down.1 = 0 then
      if v.down.2 = 0 then .star else .of ⟨WalkingCospan.right⟩
    else if v.down.2 = 0 then .of ⟨WalkingCospan.left⟩ else .of ⟨WalkingCospan.one⟩
  invFun
    | .star => ⟨(0, 0)⟩
    | .of ⟨WalkingCospan.left⟩ => ⟨(1, 0)⟩
    | .of ⟨WalkingCospan.right⟩ => ⟨(0, 1)⟩
    | .of ⟨WalkingCospan.one⟩ => ⟨(1, 1)⟩
  left_inv := by
    rintro ⟨⟨a, b⟩⟩
    fin_cases a <;> fin_cases b <;> rfl
  right_inv := by
    intro v
    cases v with
    | star => rfl
    | of v =>
      rcases v with ⟨v⟩
      cases v with
      | none => rfl
      | some v => cases v <;> rfl

private def cospanObjectEquiv : CospanObjects.{u} ≃ SSet.NativePullback.CospanObjects.{u} where
  toFun v :=
    if v.val.down.1 = 0 then ⟨WalkingCospan.right⟩
    else if v.val.down.2 = 0 then ⟨WalkingCospan.left⟩ else ⟨WalkingCospan.one⟩
  invFun
    | ⟨WalkingCospan.left⟩ => ⟨⟨(1, 0)⟩, by decide⟩
    | ⟨WalkingCospan.right⟩ => ⟨⟨(0, 1)⟩, by decide⟩
    | ⟨WalkingCospan.one⟩ => ⟨⟨(1, 1)⟩, by decide⟩
  left_inv := by
    rintro ⟨⟨⟨a, b⟩⟩, hn⟩
    fin_cases a <;> fin_cases b <;> first | rfl | exact (hn rfl).elim
  right_inv := by
    rintro ⟨v⟩
    cases v with
    | none => rfl
    | some v => cases v <;> rfl

private theorem squareForward_nonempty (x y : DiamondObjects.{u}) (h : x ≤ y) :
    Nonempty (squareObjectEquiv x ⟶ squareObjectEquiv y) := by
  rcases x with ⟨⟨a, b⟩⟩
  rcases y with ⟨⟨c, d⟩⟩
  change a.val ≤ c.val ∧ b.val ≤ d.val at h
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals
    first
    | exact ((by decide : ¬ ((1 : ℕ) ≤ 0)) h.1).elim
    | exact ((by decide : ¬ ((1 : ℕ) ≤ 0)) h.2).elim
    | exact ⟨PUnit.unit⟩
    | exact ⟨WalkingCospan.Hom.inl⟩
    | exact ⟨WalkingCospan.Hom.inr⟩
    | exact ⟨𝟙 _⟩

private def squareForwardMap (x y : DiamondObjects.{u}) (h : x ≤ y) :
    squareObjectEquiv x ⟶ squareObjectEquiv y :=
  Classical.choice (squareForward_nonempty x y h)

private theorem squareBackwardMap (x y : SSet.NativePullback.DiamondObjects.{u}) (f : x ⟶ y) :
    squareObjectEquiv.symm x ≤ squareObjectEquiv.symm y := by
  cases x with
  | star =>
    cases y with
    | star => exact le_rfl
    | of y => exact ⟨Fin.zero_le _, Fin.zero_le _⟩
  | of x =>
    cases y with
    | star => exact PEmpty.elim f
    | of y =>
      rcases x with ⟨x⟩
      rcases y with ⟨y⟩
      change WalkingCospan.Hom x y at f
      cases f with
      | id _ => exact le_rfl
      | term j =>
        cases j
        · change (1 : ℕ) ≤ 1 ∧ (0 : ℕ) ≤ 1; decide
        · change (0 : ℕ) ≤ 1 ∧ (1 : ℕ) ≤ 1; decide

private theorem cospanForward_nonempty (x y : CospanObjects.{u}) (h : x ≤ y) :
    Nonempty (cospanObjectEquiv x ⟶ cospanObjectEquiv y) := by
  rcases x with ⟨⟨⟨a, b⟩⟩, hn⟩
  rcases y with ⟨⟨⟨c, d⟩⟩, hm⟩
  change a.val ≤ c.val ∧ b.val ≤ d.val at h
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals
    first
    | exact (hn rfl).elim
    | exact (hm rfl).elim
    | exact ((by decide : ¬ ((1 : ℕ) ≤ 0)) h.1).elim
    | exact ((by decide : ¬ ((1 : ℕ) ≤ 0)) h.2).elim
    | exact ⟨WalkingCospan.Hom.inl⟩
    | exact ⟨WalkingCospan.Hom.inr⟩
    | exact ⟨𝟙 _⟩

private def cospanForwardMap (x y : CospanObjects.{u}) (h : x ≤ y) :
    cospanObjectEquiv x ⟶ cospanObjectEquiv y :=
  Classical.choice (cospanForward_nonempty x y h)

private theorem cospanBackwardMap (x y : SSet.NativePullback.CospanObjects.{u}) (f : x ⟶ y) :
    cospanObjectEquiv.symm x ≤ cospanObjectEquiv.symm y := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  change WalkingCospan.Hom x y at f
  cases f with
  | id _ => exact le_rfl
  | term j =>
    cases j
    · change (1 : ℕ) ≤ 1 ∧ (0 : ℕ) ≤ 1; decide
    · change (0 : ℕ) ≤ 1 ∧ (1 : ℕ) ≤ 1; decide

private def squareToCanonical : DiamondObjects.{u} ⥤ SSet.NativePullback.DiamondObjects.{u} where
  obj := squareObjectEquiv
  map {x y} f := squareForwardMap x y (leOfHom f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private def squareFromCanonical : SSet.NativePullback.DiamondObjects.{u} ⥤ DiamondObjects.{u} where
  obj := squareObjectEquiv.symm
  map {x y} f := homOfLE (squareBackwardMap x y f)

private def cospanToCanonical : CospanObjects.{u} ⥤ SSet.NativePullback.CospanObjects.{u} where
  obj := cospanObjectEquiv
  map {x y} f := cospanForwardMap x y (leOfHom f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private def cospanFromCanonical : SSet.NativePullback.CospanObjects.{u} ⥤ CospanObjects.{u} where
  obj := cospanObjectEquiv.symm
  map {x y} f := homOfLE (cospanBackwardMap x y f)

private def squareEquivalence : DiamondObjects.{u} ≌ SSet.NativePullback.DiamondObjects.{u} where
  functor := squareToCanonical
  inverse := squareFromCanonical
  unitIso := NatIso.ofComponents (fun x => eqToIso (squareObjectEquiv.left_inv x).symm)
    (by intros; exact Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun x => eqToIso (squareObjectEquiv.right_inv x))
    (by intros; exact Subsingleton.elim _ _)

private def cospanEquivalence : CospanObjects.{u} ≌ SSet.NativePullback.CospanObjects.{u} where
  functor := cospanToCanonical
  inverse := cospanFromCanonical
  unitIso := NatIso.ofComponents (fun x => eqToIso (cospanObjectEquiv.left_inv x).symm)
    (by intros; exact Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun x => eqToIso (cospanObjectEquiv.right_inv x))
    (by intros; exact Subsingleton.elim _ _)

private theorem inclusion_toCanonical :
    cospanInclusionFunctor.{u} ⋙ squareToCanonical =
      cospanToCanonical ⋙ SSet.NativePullback.cospanInclusionFunctor := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · rintro ⟨⟨⟨a, b⟩⟩, hn⟩
    fin_cases a <;> fin_cases b <;> first | rfl | exact (hn rfl).elim
  · intros
    exact Subsingleton.elim _ _

private def squareIso : squareShape.{u} ≅ SSet.NativePullback.squareShape.{u} where
  hom := nerveMapHomDown squareToCanonical
  inv := nerveMapHomDown squareFromCanonical
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    exact squareObjectEquiv.left_inv (s.obj i)
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    exact squareObjectEquiv.right_inv (s.obj i)

private def cospanIso : cospanShape.{u} ≅ SSet.NativePullback.cospanShape.{u} where
  hom := nerveMapHomDown cospanToCanonical
  inv := nerveMapHomDown cospanFromCanonical
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    exact cospanObjectEquiv.left_inv (s.obj i)
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    exact cospanObjectEquiv.right_inv (s.obj i)

private theorem inclusion_squareIso :
    cospanInclusion.{u} ≫ squareIso.hom =
      cospanIso.hom ≫ SSet.NativePullback.cospanInclusion := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  exact congrArg (fun F => F.obj (s.obj i)) inclusion_toCanonical

end SSet.NativePullback.Coordinate
