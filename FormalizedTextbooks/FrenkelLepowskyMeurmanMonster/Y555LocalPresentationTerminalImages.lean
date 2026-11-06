/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal terminal substitution, checking every original independent-Y555 relation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationLongestInteractions

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Substitute the proved longest word for each terminal f-generator. -/
def y555TerminalImage : Y555Vertex → BimonsterPresentation
  | none => PresentedGroup.of none
  | some (i, k) => if k = 4 then y555LocalLongest i else PresentedGroup.of (some (i, k))

/-- Terminal vertices have exactly their own preceding e-generator as a tree neighbor. -/
theorem y555Adjacent_terminal (i : Fin 3) (v : Y555Vertex) :
    y555Adjacent (some (i, 4)) v ↔ v = some (i, 3) := by
  revert i v
  decide +kernel

/-- Adjacency in the original finite tree is symmetric. -/
theorem y555Source_adjacent_symm (u v : Y555Vertex) :
    y555Adjacent u v ↔ y555Adjacent v u := by
  revert u v
  decide +kernel

/-- Each literal substituted generator is an involution in the original source group. -/
theorem y555TerminalImage_square (v : Y555Vertex) : y555TerminalImage v ^ 2 = 1 := by
  cases v with
  | none => exact y555_generator_sq none
  | some p =>
    rcases p with ⟨i, k⟩
    by_cases h : k = 4
    · simpa only [y555TerminalImage, h, ite_true, pow_two] using y555LocalLongest_square i
    · simpa only [y555TerminalImage, h, ite_false] using y555_generator_sq (some (i, k))

/-- Two commuting involutions have product square one in any genuine group. -/
theorem y555Source_commuting_square {G : Type*} [Group G] (x y : G)
    (hc : Commute x y) (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) : (x * y) ^ 2 = 1 := by
  rw [hc.mul_pow, hx, hy, one_mul]

/-- Reversing a two-factor product preserves its cubic relation by actual conjugation. -/
theorem y555Source_reverse_cube {G : Type*} [Group G] (x y : G)
    (h : (x * y) ^ 3 = 1) : (y * x) ^ 3 = 1 := by
  simpa only [mul_one, one_mul] using y555_rotate_power x y 1 3
    (by simpa only [mul_one] using h)

/-- A terminal-image product has exactly the cubic or square required by the original tree. -/
theorem y555TerminalImage_terminal_pair (i : Fin 3) (v : Y555Vertex) :
    (y555LocalLongest i * y555TerminalImage v) ^
      (if y555Adjacent (some (i, 4)) v then 3 else 2 : ℕ) = 1 := by
  by_cases he : v = some (i, 3)
  · subst v
    simpa only [y555TerminalImage, show (3 : Fin 5) ≠ 4 by decide, ite_false,
      ite_true, y555Adjacent_terminal] using y555LocalLongest_cube i
  · have ha : ¬ y555Adjacent (some (i, 4)) v :=
      fun h => he ((y555Adjacent_terminal i v).mp h)
    rw [ite_eq_right ha]
    apply y555Source_commuting_square
    · cases v with
      | none => exact y555LocalLongest_commute i none he
      | some p =>
        rcases p with ⟨j, k⟩
        by_cases hk : k = 4
        · simpa only [y555TerminalImage, hk, ite_true] using
            y555LocalLongest_pair_commute i j
        · simpa only [y555TerminalImage, hk, ite_false] using
            y555LocalLongest_commute i (some (j, k)) he
    · simpa only [pow_two] using y555LocalLongest_square i
    · exact y555TerminalImage_square v

/-- Every distinct Coxeter pair remains valid after the literal terminal substitution. -/
theorem y555TerminalImage_coxeter (u v : Y555Vertex) (huv : u ≠ v) :
    (y555TerminalImage u * y555TerminalImage v) ^
      (if y555Adjacent u v then 3 else 2 : ℕ) = 1 := by
  have left (i : Fin 3) (h : u = some (i, 4)) :
      (y555TerminalImage u * y555TerminalImage v) ^
        (if y555Adjacent u v then 3 else 2 : ℕ) = 1 := by
    subst u
    simpa only [y555TerminalImage, ite_true] using y555TerminalImage_terminal_pair i v
  have right (i : Fin 3) (h : v = some (i, 4)) :
      (y555TerminalImage u * y555TerminalImage v) ^
        (if y555Adjacent u v then 3 else 2 : ℕ) = 1 := by
    subst v
    by_cases ha : y555Adjacent u (some (i, 4))
    · have h := y555TerminalImage_terminal_pair i u
      have hb := (y555Source_adjacent_symm u (some (i, 4))).mp ha
      simp only [ite_eq_left hb] at h
      simpa only [y555TerminalImage, ite_true, ite_eq_left ha] using
        y555Source_reverse_cube _ _ h
    · have hb : ¬ y555Adjacent (some (i, 4)) u :=
        fun h => ha ((y555Source_adjacent_symm u (some (i, 4))).mpr h)
      have h := y555TerminalImage_terminal_pair i u
      simp only [ite_eq_right hb] at h
      have hr := congrArg (MulAut.conj (y555LocalLongest i)⁻¹) h
      simpa [map_pow, map_one, MulAut.conj_apply, mul_assoc,
        y555TerminalImage, ite_eq_right ha] using hr
  cases u with
  | none =>
    cases v with
    | none => exact False.elim (huv rfl)
    | some p =>
      rcases p with ⟨j, l⟩
      by_cases h : l = 4
      · exact right j (by simp only [h])
      · simpa only [y555TerminalImage, h, ite_false] using
          y555_coxeter_relation none (some (j, l)) huv
  | some p =>
    rcases p with ⟨i, k⟩
    by_cases hk : k = 4
    · exact left i (by simp only [hk])
    · cases v with
      | none =>
        simpa only [y555TerminalImage, hk, ite_false] using
          y555_coxeter_relation (some (i, k)) none huv
      | some q =>
        rcases q with ⟨j, l⟩
        by_cases hl : l = 4
        · exact right j (by simp only [hl])
        · simpa only [y555TerminalImage, hk, hl, ite_false] using
            y555_coxeter_relation (some (i, k)) (some (j, l)) huv

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
