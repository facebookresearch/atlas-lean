/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedInteractionCore









open scoped BigOperators
open Finset

namespace StatMech.FrontierD

noncomputable section

variable {L : Nat} [Fact (8 < L)]

local instance : Fact (2 < L) :=
  ⟨lt_trans (by omega) (Fact.out : 8 < L)⟩

theorem fkRectIntegralSquareDartTranslate_comp
    (u v : Int × Int) (d : FKRectIntegralSquareDart) :
    fkRectIntegralSquareDartTranslate u
        (fkRectIntegralSquareDartTranslate v d) =
      fkRectIntegralSquareDartTranslate (v.1 + u.1, v.2 + u.2) d := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  apply Prod.ext
  · apply Prod.ext <;>
      simp [fkRectIntegralSquareDartTranslate] <;> ring
  · rfl



theorem fkRectRefinedRawInteraction_integralTranslate_relative
    (a b : List FKRectIntegralSquareDart) (u v : Int × Int) :
    fkRectRefinedRawInteraction
        ((a.map (fkRectIntegralSquareDartTranslate u)).map
          (fkRectIntegralSquareDartMod L))
        ((b.map (fkRectIntegralSquareDartTranslate v)).map
          (fkRectIntegralSquareDartMod L)) =
      fkRectRefinedRawInteraction
        (a.map (fkRectIntegralSquareDartMod L))
        ((b.map (fkRectIntegralSquareDartTranslate
            (v.1 - u.1, v.2 - u.2))).map
          (fkRectIntegralSquareDartMod L)) := by
  have h := fkRectRefinedRawInteraction_integralTranslate
    (L := L) (-u.1, -u.2)
    (a.map (fkRectIntegralSquareDartTranslate u))
    (b.map (fkRectIntegralSquareDartTranslate v))
  have ha (d : FKRectIntegralSquareDart) :
      fkRectIntegralSquareDartTranslate (-u.1, -u.2)
        (fkRectIntegralSquareDartTranslate u d) = d := by
    rw [fkRectIntegralSquareDartTranslate_comp]
    simp [fkRectIntegralSquareDartTranslate]
  have hb (d : FKRectIntegralSquareDart) :
      fkRectIntegralSquareDartTranslate (-u.1, -u.2)
        (fkRectIntegralSquareDartTranslate v d) =
      fkRectIntegralSquareDartTranslate (v.1 - u.1, v.2 - u.2) d := by
    rw [fkRectIntegralSquareDartTranslate_comp]
    congr 2 <;> simp
  have hmapa :
      ((a.map (fkRectIntegralSquareDartTranslate u)).map
          (fkRectIntegralSquareDartTranslate (-u.1, -u.2))).map
          (fkRectIntegralSquareDartMod L) =
        a.map (fkRectIntegralSquareDartMod L) := by
    simp only [List.map_map]
    congr 1
    funext d
    exact congrArg (fkRectIntegralSquareDartMod L) (ha d)
  have hmapb :
      ((b.map (fkRectIntegralSquareDartTranslate v)).map
          (fkRectIntegralSquareDartTranslate (-u.1, -u.2))).map
          (fkRectIntegralSquareDartMod L) =
        (b.map (fkRectIntegralSquareDartTranslate
          (v.1 - u.1, v.2 - u.2))).map
            (fkRectIntegralSquareDartMod L) := by
    simp only [List.map_map]
    congr 1
    funext d
    exact congrArg (fkRectIntegralSquareDartMod L) (hb d)
  rw [hmapa, hmapb] at h
  exact h.symm


theorem fkRectRefinedRawInteraction_repeatTranslated_left
    (l : List FKRectIntegralSquareDart) (u : Int × Int) (n : Nat)
    (b : List (StatMech.Onsager.ons_Dart L)) :
    fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath l u n).map
          (fkRectIntegralSquareDartMod L)) b =
      ∑ k ∈ range n,
        fkRectRefinedRawInteraction
          ((l.map (fkRectIntegralSquareDartTranslate
              (fkRectNatScale k u))).map
            (fkRectIntegralSquareDartMod L)) b := by
  induction n with
  | zero => simp [fkRectRepeatTranslatedDartPath,
      fkRectRefinedRawInteraction]
  | succ n ih =>
      rw [fkRectRepeatTranslatedDartPath, List.map_append,
        fkRectRefinedRawInteraction_append_left, ih, sum_range_succ]


theorem fkRectRefinedRawInteraction_repeatTranslated_right
    (a : List (StatMech.Onsager.ons_Dart L))
    (l : List FKRectIntegralSquareDart) (u : Int × Int) (n : Nat) :
    fkRectRefinedRawInteraction a
        ((fkRectRepeatTranslatedDartPath l u n).map
          (fkRectIntegralSquareDartMod L)) =
      ∑ k ∈ range n,
        fkRectRefinedRawInteraction a
          ((l.map (fkRectIntegralSquareDartTranslate
              (fkRectNatScale k u))).map
            (fkRectIntegralSquareDartMod L)) := by
  induction n with
  | zero => simp [fkRectRepeatTranslatedDartPath,
      fkRectRefinedRawInteraction]
  | succ n ih =>
      rw [fkRectRepeatTranslatedDartPath, List.map_append,
        fkRectRefinedRawInteraction_append_right, ih, sum_range_succ]



theorem fkRectRefinedRawInteraction_repeatTranslated_both
    (a b : List FKRectIntegralSquareDart)
    (u v : Int × Int) (n m : Nat) :
    fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath a u n).map
          (fkRectIntegralSquareDartMod L))
        ((fkRectRepeatTranslatedDartPath b v m).map
          (fkRectIntegralSquareDartMod L)) =
      ∑ i ∈ range n, ∑ j ∈ range m,
        fkRectRefinedRawInteraction
          ((a.map (fkRectIntegralSquareDartTranslate
              (fkRectNatScale i u))).map
            (fkRectIntegralSquareDartMod L))
          ((b.map (fkRectIntegralSquareDartTranslate
              (fkRectNatScale j v))).map
            (fkRectIntegralSquareDartMod L)) := by
  rw [fkRectRefinedRawInteraction_repeatTranslated_left]
  apply sum_congr rfl
  intro i hi
  rw [fkRectRefinedRawInteraction_repeatTranslated_right]

end

end StatMech.FrontierD
