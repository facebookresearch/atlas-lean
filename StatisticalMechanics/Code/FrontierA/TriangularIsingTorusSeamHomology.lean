/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusSpinGauge
import Code.FrontierA.TriangularIsingTorusHomology








namespace StatMech.FrontierA

open StatMech.Onsager



theorem triangularTorusXSeamEdge_dart_iff
    (L : Nat) [Fact (2 < L)] (d : triangularTorusDart L) :
    triangularTorusXSeamEdge L (triangularTorusDartEquiv L d).edge ↔
      ons_xWrap (triangularTorusXMovementDart L d) := by
  have h1 : (1 : ZMod L) ≠ 0 := by
    letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
    exact one_ne_zero
  have h2 : (2 : ZMod L) ≠ 0 := by
    rw [Ne, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have := (Fact.out : 2 < L)
    omega
  rcases d with ⟨p, mu⟩
  fin_cases mu
  all_goals simp [triangularTorusXSeamEdge,
      triangularTorusDartEquiv_apply,
      triangularTorusDartToGraphDart, SimpleGraph.Dart.edge,
      triangularTorusDirectionStep, triangularTorusXMovementDart,
      triangularTorusXMovementDirection, ons_xWrap, ons_xSeamEdge,
      Prod.ext_iff]
  · constructor
    · rintro (⟨y, h | h⟩ | ⟨y, h | h⟩)
      · exact h.1
      · rcases h with ⟨⟨hx, -⟩, hx', -⟩
        exfalso
        apply h2
        linear_combination hx - hx'
      · exact h.1.1
      · rcases h with ⟨⟨hx, -⟩, hx', -⟩
        exfalso
        apply h2
        linear_combination hx - hx'
    · intro hp
      exact Or.inl ⟨p.2, Or.inl ⟨hp, rfl⟩⟩
  · constructor
    · rintro (⟨y, h | h⟩ | ⟨y, h | h⟩)
      · rcases h with ⟨⟨hx, -⟩, hx', -⟩
        exfalso
        apply h2
        linear_combination hx' - hx
      · exact h.1.1
      · rcases h with ⟨⟨hx, -⟩, hx', -⟩
        exfalso
        apply h2
        linear_combination hx' - hx
      · exact h.1.1
    · intro hp
      exact Or.inl ⟨p.2, Or.inr ⟨⟨hp, rfl⟩, by simp [hp]⟩⟩
  · aesop
  · aesop
  · constructor
    · rintro (⟨y, h | h⟩ | ⟨y, h | h⟩)
      · exact h.1.1
      · rcases h with ⟨⟨hx, -⟩, hx', -⟩
        exfalso
        apply h2
        linear_combination hx - hx'
      · exact h.1
      · rcases h with ⟨⟨hx, -⟩, hx', -⟩
        exfalso
        apply h2
        linear_combination hx - hx'
    · intro hp
      exact Or.inr ⟨p.2, Or.inl ⟨hp, rfl⟩⟩
  · constructor
    · rintro (⟨y, h | h⟩ | ⟨y, h | h⟩)
      · rcases h with ⟨⟨hx, -⟩, hx', -⟩
        exfalso
        apply h2
        linear_combination hx' - hx
      · exact h.1.1
      · rcases h with ⟨⟨hx, -⟩, hx', -⟩
        exfalso
        apply h2
        linear_combination hx' - hx
      · exact h.1.1
    · intro hp
      exact Or.inr ⟨p.2 + 1, Or.inr (by simp [hp])⟩



theorem triangularTorusYSeamEdge_dart_iff
    (L : Nat) [Fact (2 < L)] (d : triangularTorusDart L) :
    triangularTorusYSeamEdge L (triangularTorusDartEquiv L d).edge ↔
      ons_yWrap (triangularTorusYMovementDart L d) := by
  have h1 : (1 : ZMod L) ≠ 0 := by
    letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
    exact one_ne_zero
  have h2 : (2 : ZMod L) ≠ 0 := by
    rw [Ne, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have := (Fact.out : 2 < L)
    omega
  rcases d with ⟨p, mu⟩
  fin_cases mu
  all_goals simp [triangularTorusYSeamEdge,
      triangularTorusDartEquiv_apply,
      triangularTorusDartToGraphDart, SimpleGraph.Dart.edge,
      triangularTorusDirectionStep, triangularTorusYMovementDart,
      triangularTorusYMovementDirection, ons_yWrap, ons_ySeamEdge,
      Prod.ext_iff]
  · aesop
  · aesop
  · constructor
    · rintro (⟨x, h | h⟩ | ⟨x, h | h⟩)
      · exact h.2
      · rcases h with ⟨⟨-, hy⟩, -, hy'⟩
        exfalso
        apply h2
        linear_combination hy - hy'
      · exact h.1.2
      · rcases h with ⟨⟨-, hy⟩, -, hy'⟩
        exfalso
        apply h2
        linear_combination hy - hy'
    · intro hp
      exact Or.inl ⟨p.1, Or.inl ⟨rfl, hp⟩⟩
  · constructor
    · rintro (⟨x, h | h⟩ | ⟨x, h | h⟩)
      · rcases h with ⟨⟨-, hy⟩, -, hy'⟩
        exfalso
        apply h2
        linear_combination hy' - hy
      · exact h.1.2
      · rcases h with ⟨⟨-, hy⟩, -, hy'⟩
        exfalso
        apply h2
        linear_combination hy' - hy
      · exact h.1.2
    · intro hp
      exact Or.inl ⟨p.1, Or.inr ⟨⟨rfl, hp⟩, by simp [hp]⟩⟩
  · constructor
    · rintro (⟨x, h | h⟩ | ⟨x, h | h⟩)
      · exact h.1.2
      · rcases h with ⟨⟨-, hy⟩, -, hy'⟩
        exfalso
        apply h2
        linear_combination hy - hy'
      · exact h.2
      · rcases h with ⟨⟨-, hy⟩, -, hy'⟩
        exfalso
        apply h2
        linear_combination hy - hy'
    · intro hp
      exact Or.inr ⟨p.1, Or.inl ⟨rfl, hp⟩⟩
  · constructor
    · rintro (⟨x, h | h⟩ | ⟨x, h | h⟩)
      · rcases h with ⟨⟨-, hy⟩, -, hy'⟩
        exfalso
        apply h2
        linear_combination hy' - hy
      · exact h.1.2
      · rcases h with ⟨⟨-, hy⟩, -, hy'⟩
        exfalso
        apply h2
        linear_combination hy' - hy
      · exact h.1.2
    · intro hp
      exact Or.inr ⟨p.1 + 1, Or.inr (by simp [hp])⟩



theorem triangularTorusSpinDartSeamSign_eq_surfaceHomologyCharacter
    (L : Nat) [Fact (2 < L)] (a b : Fin 2)
    (d : triangularTorusDart L) :
    triangularTorusSpinDartSeamSign L a b d =
      surfaceHomologyCharacter (fun _ => a, fun _ => b)
        (triangularTorusSurfaceEdgeClass L
          (triangularTorusDartEquiv L d).edge) := by
  unfold triangularTorusSurfaceEdgeClass
  simp only [triangularTorusXSeamEdge_dart_iff L d,
    triangularTorusYSeamEdge_dart_iff L d]
  rcases d with ⟨p, mu⟩
  fin_cases a <;> fin_cases b <;> fin_cases mu <;>
    simp [triangularTorusSpinDartSeamSign,
      surfaceHomologyCharacter, surfaceSpinLinearParity,
      surfaceParitySign, triangularTorusXMovementDart,
      triangularTorusYMovementDart, triangularTorusXMovementDirection,
      triangularTorusYMovementDirection, ons_xWrap, ons_yWrap,
      ons_xWrapSign, ons_yWrapSign, Fin.val_add] <;>
    split_ifs <;> norm_num

end StatMech.FrontierA
