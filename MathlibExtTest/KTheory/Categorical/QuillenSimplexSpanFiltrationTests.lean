/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.KTheory.Exact.Quillen.QuillenSimplexSpanFiltration

/-!
# Tests for Quillen simplex span filtrations

These tests pin Prop-valued presentation existence, right-associated interval
and tail representatives, quotient-class order, and the literal edgewise
kernel/apex filtration in degrees zero through three.  In degree two the long
span is definitionally the ordered composite `Span.comp S01 S12`; in degree
three the parentheses are fixed on the right.

No chosen public presentation, Stage completion, grid lift, fiber,
contractibility, realization, or Q/S comparison is exercised here.
-/

noncomputable section

open CategoryTheory Limits ZeroObject
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace MathlibExtTest.KTheory.Categorical
namespace QuillenSimplexSpanFiltrationTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance quillenSimplexSpanFiltrationTestsWaldhausenC :
    WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

example {a : SimplexCategory} (q : QuillenQSimplex C a) :
    Nonempty (QuillenSimplexSpanPresentation q) :=
  QuillenSimplexSpanPresentation.nonempty q

section ArbitraryDegree

variable {a : SimplexCategory} (q : QuillenQSimplex C a)
  (P : QuillenSimplexSpanPresentation q)

example (i : Fin a.len) :
    QuillenSpan (q.obj' i.val (by omega)).obj
      (q.obj' (i.val + 1) (by omega)).obj :=
  P.span i

example (i : Fin a.len) : QuillenSpanFlagData (P.span i) :=
  P.flag i

example (i : Fin a.len) :
    QuillenQ.mkHom (P.span i) =
      q.map' i.val (i.val + 1) (by omega) (by omega) :=
  P.class_eq i

example (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    QuillenSpan (q.obj k).obj (q.obj l).obj :=
  P.intervalSpan k l hkl

example (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    QuillenQ.mkHom (P.intervalSpan k l hkl) = q.map (homOfLE hkl) :=
  P.intervalSpan_mkHom k l hkl

example (k : Fin (a.len + 1)) :
    QuillenQ.mkHom (P.tailSpan k) = q.map (homOfLE (Fin.le_last k)) :=
  P.tailSpan_mkHom k

example : IsZero (P.filtration.chain.obj 0) :=
  P.filtration.first_isZero

example (i : Fin (edgewiseQ.obj a).len) :
    IsAdmissibleMono
      (P.filtration.chain.map' i.val (i.val + 1) (by omega) (by omega)) :=
  P.filtration.step_admissible i

example (k : Fin a.len) :
    P.filtration.chain.obj (edgewiseLeftIndex a k.castSucc) =
      (P.tailKernelPresentation k).kernel :=
  P.filtration_chain_obj_left k

example :
    P.filtration.chain.obj (edgewiseLeftIndex a (Fin.last a.len)) =
      (0 : C) :=
  P.filtration_chain_obj_left_last

example (k : Fin (a.len + 1)) :
    P.filtration.chain.obj (edgewiseRightIndex a k) =
      P.rightTailObject k :=
  P.filtration_chain_obj_right k

end ArbitraryDegree

section DegreeZero

variable (q0 : QuillenQSimplex C ⦋0⦌)
  (P0 : QuillenSimplexSpanPresentation q0)

example : (edgewiseLeftIndex ⦋0⦌ (0 : Fin 1)).val = 0 := by simp
example : (edgewiseRightIndex ⦋0⦌ (0 : Fin 1)).val = 1 := by simp

example :
    P0.filtration.chain.obj (edgewiseLeftIndex ⦋0⦌ (0 : Fin 1)) =
      (0 : C) :=
  P0.filtration_chain_obj_left_last

example :
    P0.filtration.chain.obj (edgewiseRightIndex ⦋0⦌ (0 : Fin 1)) =
      (q0.obj 0).obj := by
  rw [P0.filtration_chain_obj_right]
  have h : (0 : Fin 1) = Fin.last 0 := by ext; rfl
  simpa only [h] using P0.rightTailObject_last

example : IsAdmissibleMono
    (P0.filtration.chain.map' 0 1 (by simp) (by simp)) :=
  P0.filtration.step_admissible ⟨0, by simp⟩

end DegreeZero

section DegreeOne

variable (q1 : QuillenQSimplex C ⦋1⦌)
  (P1 : QuillenSimplexSpanPresentation q1)

example :
    P1.intervalSpan (0 : Fin 2) (1 : Fin 2) (by decide) = P1.span 0 :=
  P1.intervalSpan_adjacent 0

example :
    P1.filtration.chain.obj (edgewiseLeftIndex ⦋1⦌ (1 : Fin 2)) =
      (0 : C) :=
  P1.filtration_chain_obj_left_last

example :
    P1.filtration.chain.obj (edgewiseLeftIndex ⦋1⦌ (0 : Fin 2)) =
      (P1.tailKernelPresentation (0 : Fin 1)).kernel :=
  P1.filtration_chain_obj_left 0

example :
    P1.filtration.chain.obj (edgewiseRightIndex ⦋1⦌ (0 : Fin 2)) =
      P1.rightTailObject 0 :=
  P1.filtration_chain_obj_right 0

example :
    P1.filtration.chain.obj (edgewiseRightIndex ⦋1⦌ (1 : Fin 2)) =
      (q1.obj 1).obj := by
  rw [P1.filtration_chain_obj_right]
  have h : (1 : Fin 2) = Fin.last 1 := by ext; rfl
  simpa only [h] using P1.rightTailObject_last

end DegreeOne

section DegreeTwo

variable (q2 : QuillenQSimplex C ⦋2⦌)
  (P2 : QuillenSimplexSpanPresentation q2)

/-- The decisive low-degree regression: no identity factor and no opposite
parenthesization occurs in the long span. -/
example :
    P2.intervalSpan (0 : Fin 2).castSucc (2 : Fin 3) (by decide) =
      Span.comp (P2.span (0 : Fin 2)) (P2.span (1 : Fin 2)) := by
  rw [P2.intervalSpan_of_gap (0 : Fin 2) (2 : Fin 3) (by decide)]
  have hAdj :
      P2.intervalSpan (0 : Fin 2).succ (2 : Fin 3) (by decide) =
        P2.span (1 : Fin 2) := by
    have h : (0 : Fin 2).succ = (1 : Fin 2).castSucc := by ext; rfl
    cases h
    exact P2.intervalSpan_adjacent (1 : Fin 2)
  rw [hAdj]

example :
    QuillenQ.mkHom (P2.intervalSpan (0 : Fin 3) (2 : Fin 3) (by decide)) =
      q2.map' 0 2 (by decide) (by decide) := by
  simpa only [ComposableArrows.map'] using
    P2.intervalSpan_mkHom (0 : Fin 3) (2 : Fin 3) (by decide)

example :
    QuillenQ.mkHom (P2.intervalSpan (0 : Fin 3) (2 : Fin 3) (by decide)) =
      q2.map' 0 1 (by decide) (by decide) ≫
        q2.map' 1 2 (by decide) (by decide) := by
  rw [P2.intervalSpan_mkHom]
  exact q2.map'_comp 0 1 2

/-- The six displayed filtration objects are
`0, K(1,2), K(0,2), M(0,2), M(1,2), X(2)`. -/
example :
    P2.filtration.chain.obj (edgewiseLeftIndex ⦋2⦌ (2 : Fin 3)) =
      (0 : C) :=
  P2.filtration_chain_obj_left_last

example :
    P2.filtration.chain.obj (edgewiseLeftIndex ⦋2⦌ (1 : Fin 3)) =
      (P2.tailKernelPresentation (1 : Fin 2)).kernel :=
  P2.filtration_chain_obj_left 1

example :
    P2.filtration.chain.obj (edgewiseLeftIndex ⦋2⦌ (0 : Fin 3)) =
      (P2.tailKernelPresentation (0 : Fin 2)).kernel :=
  P2.filtration_chain_obj_left 0

example :
    P2.filtration.chain.obj (edgewiseRightIndex ⦋2⦌ (0 : Fin 3)) =
      P2.rightTailObject 0 :=
  P2.filtration_chain_obj_right 0

example :
    P2.filtration.chain.obj (edgewiseRightIndex ⦋2⦌ (1 : Fin 3)) =
      P2.rightTailObject 1 :=
  P2.filtration_chain_obj_right 1

example :
    P2.filtration.chain.obj (edgewiseRightIndex ⦋2⦌ (2 : Fin 3)) =
      (q2.obj 2).obj := by
  rw [P2.filtration_chain_obj_right]
  have h : (2 : Fin 3) = Fin.last 2 := by ext; rfl
  simpa only [h] using P2.rightTailObject_last

example (k : Fin 3) :
    (edgewiseLeftIndex ⦋2⦌ k).val = 2 - k.val := by simp

example (k : Fin 3) :
    (edgewiseRightIndex ⦋2⦌ k).val = 3 + k.val := by
  simp [Nat.add_comm]

example (i : Fin (edgewiseQ.obj ⦋2⦌).len) :
    IsAdmissibleMono
      (P2.filtration.chain.map' i.val (i.val + 1) (by omega) (by omega)) :=
  P2.filtration.step_admissible i

end DegreeTwo

section DegreeThree

variable (q3 : QuillenQSimplex C ⦋3⦌)
  (P3 : QuillenSimplexSpanPresentation q3)

/-- Degree three fixes right association rather than silently using the
bicategorical associator in the representative definition. -/
example :
    P3.intervalSpan (0 : Fin 3).castSucc (3 : Fin 4) (by decide) =
      Span.comp (P3.span (0 : Fin 3))
        (Span.comp (P3.span (1 : Fin 3)) (P3.span (2 : Fin 3))) := by
  rw [P3.intervalSpan_of_gap (0 : Fin 3) (3 : Fin 4) (by decide)]
  have h23 :
      P3.intervalSpan (1 : Fin 3).succ (3 : Fin 4) (by decide) =
        P3.span (2 : Fin 3) := by
    have h2 : (1 : Fin 3).succ = (2 : Fin 3).castSucc := by ext; rfl
    cases h2
    exact P3.intervalSpan_adjacent (2 : Fin 3)
  have h13 :
      P3.intervalSpan (1 : Fin 3).castSucc (3 : Fin 4) (by decide) =
        Span.comp (P3.span (1 : Fin 3)) (P3.span (2 : Fin 3)) := by
    rw [P3.intervalSpan_of_gap (1 : Fin 3) (3 : Fin 4) (by decide), h23]
  have hRest :
      P3.intervalSpan (0 : Fin 3).succ (3 : Fin 4) (by decide) =
        Span.comp (P3.span (1 : Fin 3)) (P3.span (2 : Fin 3)) := by
    have h1 : (0 : Fin 3).succ = (1 : Fin 3).castSucc := by ext; rfl
    cases h1
    exact h13
  rw [hRest]

end DegreeThree

end QuillenSimplexSpanFiltrationTests
end MathlibExtTest.KTheory.Categorical

end
