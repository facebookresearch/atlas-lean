/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Pairwise commutation and exact e-cubics of the actual independent-Y444 longest words. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationY444C431

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Three genuine cyclic source endomorphisms act as the identity on independent Y444. -/
theorem y444CycleHom_three :
    y444CycleHom.comp (y444CycleHom.comp y444CycleHom) = MonoidHom.id Y444Presentation := by
  apply PresentedGroup.ext
  intro v
  simp only [MonoidHom.comp_apply, y444CycleHom_generator, y444VertexCycle_three,
    MonoidHom.id_apply]

/-- Cycling the third longest word returns the original first longest word. -/
theorem y444CycleHom_localF3 : y444CycleHom y444LocalF3 = y444LocalF1 := by
  have h := congrArg (fun f : Y444Presentation →* Y444Presentation =>
    f y444LocalF1) y444CycleHom_three
  simpa only [y444LocalF3, y444LocalF2, MonoidHom.comp_apply, MonoidHom.id_apply] using h

/-- The first longest word commutes with the literal second longest word's seven generators. -/
theorem y444LocalF1_commute_F2 : Commute y444LocalF1 y444LocalF2 := by
  rw [y444LocalF2_word21]
  exact ((((((y444LocalF1_commute none (by decide)).mul_right
    (y444LocalF1_commute (some (1, 0)) (by decide))).mul_right
    (y444LocalF1_commute (some (0, 0)) (by decide))).mul_right
    (y444LocalF1_commute (some (2, 0)) (by decide))).mul_right
    (y444LocalF1_commute (some (1, 1)) (by decide))).mul_right
    (y444LocalF1_commute (some (0, 1)) (by decide))).mul_right
    (y444LocalF1_commute (some (1, 2)) (by decide)) |>.pow_right 9

/-- The second and third actual longest words commute by genuine cyclic symmetry. -/
theorem y444LocalF2_commute_F3 : Commute y444LocalF2 y444LocalF3 := by
  simpa only [y444LocalF2, y444LocalF3] using y444LocalF1_commute_F2.map y444CycleHom

/-- The third and first actual longest words commute by genuine cyclic symmetry. -/
theorem y444LocalF3_commute_F1 : Commute y444LocalF3 y444LocalF1 := by
  have h := y444LocalF2_commute_F3.map y444CycleHom
  change Commute y444LocalF3 (y444CycleHom y444LocalF3) at h
  rw [y444CycleHom_localF3] at h
  exact h

/-- The three actual longest involutions indexed by their original source arms. -/
def y444LocalLongest : Fin 3 → Y444Presentation := ![y444LocalF1, y444LocalF2, y444LocalF3]

/-- Every indexed actual longest word is an involution. -/
theorem y444LocalLongest_square (i : Fin 3) : y444LocalLongest i * y444LocalLongest i = 1 := by
  fin_cases i
  · exact y444LocalF1_square
  · exact y444LocalF2_square
  · exact y444LocalF3_square

/-- Every indexed longest word satisfies the proved cubic with its own source e-generator. -/
theorem y444LocalLongest_cube (i : Fin 3) :
    (y444LocalLongest i * (PresentedGroup.of (some (i, 3)) : Y444Presentation)) ^ 3 = 1 := by
  fin_cases i
  · exact y444LocalF1_e1_cube
  · exact y444LocalF2_e2_cube
  · exact y444LocalF3_e3_cube

/-- Each indexed longest word commutes with all original vertices except its own e-generator. -/
theorem y444LocalLongest_commute (i : Fin 3) (v : Y444Vertex) (hv : v ≠ some (i, 3)) :
    Commute (y444LocalLongest i) (PresentedGroup.of v) := by
  fin_cases i
  · exact y444LocalF1_commute v hv
  · exact y444LocalF2_commute v hv
  · exact y444LocalF3_commute v hv

/-- All three indexed actual longest words commute pairwise, including equal indices. -/
theorem y444LocalLongest_pair_commute (i j : Fin 3) :
    Commute (y444LocalLongest i) (y444LocalLongest j) := by
  fin_cases i <;> fin_cases j
  · exact Commute.refl _
  · exact y444LocalF1_commute_F2
  · exact y444LocalF3_commute_F1.symm
  · exact y444LocalF1_commute_F2.symm
  · exact Commute.refl _
  · exact y444LocalF2_commute_F3
  · exact y444LocalF3_commute_F1
  · exact y444LocalF2_commute_F3.symm
  · exact Commute.refl _


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
