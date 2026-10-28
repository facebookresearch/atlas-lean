/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Original C522 Coxeter and spider relations plus the already proved longest-word cubic.
The additional cubic is a checked consequence in independent Y555, never a recognition axiom. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTerminalKernel

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact C522 source vertices, with original f1 last and the nine C422 vertices first. -/
def y522Vertex : Fin 10 → Y555Vertex :=
  ![none, some (0, 0), some (0, 1), some (0, 2), some (0, 3),
    some (1, 0), some (1, 1), some (2, 0), some (2, 1), some (0, 4)]

/-- These ten actual source vertices are distinct. -/
theorem y522Vertex_injective : Function.Injective y522Vertex := by decide +kernel

/-- The exact corrected first longest word in the ten-generator source alphabet. -/
def y522F12 : FreeGroup (Fin 10) :=
  (FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 5 * FreeGroup.of 7 *
    FreeGroup.of 2 * FreeGroup.of 6 * FreeGroup.of 3) ^ 9

/-- The literal original spider, with all three source c-generators present. -/
def y522Spider : FreeGroup (Fin 10) :=
  FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 2 *
    FreeGroup.of 0 * FreeGroup.of 5 * FreeGroup.of 6 *
      FreeGroup.of 0 * FreeGroup.of 7 * FreeGroup.of 8

/-- The source cubic Q whose actual Y555 validity has already been independently certified. -/
def y522Cubic : FreeGroup (Fin 10) := (y522F12 * FreeGroup.of 4) ^ 3

/-- Original squares and all Coxeter pairs, original spider10, and the proved Q consequence. -/
def y522Relations : Set (FreeGroup (Fin 10)) :=
  {w | (∃ v, w = FreeGroup.of v ^ 2) ∨
    (∃ u v, u ≠ v ∧ w = (FreeGroup.of u * FreeGroup.of v) ^
      (if y555Adjacent (y522Vertex u) (y522Vertex v) then 3 else 2 : ℕ)) ∨
        w = y522Spider ^ 10 ∨ w = y522Cubic}

/-- Evaluation of the literal source longest word is the genuine original F1. -/
theorem y522F12_source_value :
    FreeGroup.lift (fun v => (PresentedGroup.of (y522Vertex v) : BimonsterPresentation))
      y522F12 = y555LocalF1 := by
  rw [y555LocalF1_word12]
  simp [y522F12, y522Vertex, y555LocalRestrictedWord, y555LocalF1Support12,
    y322Vertex, map_pow, map_mul, FreeGroup.lift_apply_of, mul_assoc]

/-- Every exact local relation holds in the original independent Y555 presentation. -/
theorem y522Relations_valid (r : FreeGroup (Fin 10)) (hr : r ∈ y522Relations) :
    FreeGroup.lift (fun v => (PresentedGroup.of (y522Vertex v) : BimonsterPresentation)) r = 1 := by
  rcases hr with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩ | rfl | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of] using y555_generator_sq (y522Vertex v)
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of] using
      y555_coxeter_relation (y522Vertex u) (y522Vertex v)
        (fun h => huv (y522Vertex_injective h))
  · have h := PresentedGroup.one_of_mem (rels := y555Relations)
      (show y555Spider ^ 10 ∈ y555Relations from Or.inr (Or.inr rfl))
    simpa [y522Spider, y555Spider, y522Vertex, map_pow, map_mul,
      FreeGroup.lift_apply_of, PresentedGroup.of, mul_assoc] using h
  · rw [y522Cubic, map_pow, map_mul, y522F12_source_value, FreeGroup.lift_apply_of]
    change (y555LocalF1 * (PresentedGroup.of (some (0, 3)) : BimonsterPresentation)) ^ 3 = 1
    exact y555LocalF1_e1_cube


/-- All nine coefficient generators are original nonterminal vertices fixed by substitution. -/
theorem y522Nonterminal_fixed (i : Fin 9) :
    y555TerminalHom (PresentedGroup.of (y522Vertex i.castSucc)) =
      (PresentedGroup.of (y522Vertex i.castSucc) : BimonsterPresentation) := by
  rw [y555TerminalHom_generator]
  fin_cases i <;> rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
