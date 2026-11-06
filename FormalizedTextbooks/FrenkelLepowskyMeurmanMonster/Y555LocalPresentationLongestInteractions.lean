/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Pairwise commutation of the three actual longest words inside independent Y555. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationLongestCubeRotation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Cycling the third longest word returns the original first longest word. -/
theorem y555CycleHom_localF3 : y555CycleHom y555LocalF3 = y555LocalF1 := by
  have h := congrArg (fun f : BimonsterPresentation →* BimonsterPresentation =>
    f y555LocalF1) y555CycleHom_three
  simpa only [y555LocalF3, y555LocalF2, MonoidHom.comp_apply, MonoidHom.id_apply] using h

/-- The first longest word commutes with the literal second longest word's seven generators. -/
theorem y555LocalF1_commute_F2 : Commute y555LocalF1 y555LocalF2 := by
  rw [y555LocalF2_word21]
  exact ((((((y555LocalF1_commute none (by decide)).mul_right
    (y555LocalF1_commute (some (1, 0)) (by decide))).mul_right
    (y555LocalF1_commute (some (0, 0)) (by decide))).mul_right
    (y555LocalF1_commute (some (2, 0)) (by decide))).mul_right
    (y555LocalF1_commute (some (1, 1)) (by decide))).mul_right
    (y555LocalF1_commute (some (0, 1)) (by decide))).mul_right
    (y555LocalF1_commute (some (1, 2)) (by decide)) |>.pow_right 9

/-- The second and third actual longest words commute by genuine cyclic symmetry. -/
theorem y555LocalF2_commute_F3 : Commute y555LocalF2 y555LocalF3 := by
  simpa only [y555LocalF2, y555LocalF3] using y555LocalF1_commute_F2.map y555CycleHom

/-- The third and first actual longest words commute by genuine cyclic symmetry. -/
theorem y555LocalF3_commute_F1 : Commute y555LocalF3 y555LocalF1 := by
  have h := y555LocalF2_commute_F3.map y555CycleHom
  change Commute y555LocalF3 (y555CycleHom y555LocalF3) at h
  rw [y555CycleHom_localF3] at h
  exact h

/-- The three actual longest involutions indexed by their original source arms. -/
def y555LocalLongest : Fin 3 → BimonsterPresentation := ![y555LocalF1, y555LocalF2, y555LocalF3]

/-- Every indexed actual longest word is an involution. -/
theorem y555LocalLongest_square (i : Fin 3) : y555LocalLongest i * y555LocalLongest i = 1 := by
  fin_cases i
  · exact y555LocalF1_square
  · exact y555LocalF2_square
  · exact y555LocalF3_square

/-- Every indexed longest word satisfies the proved cubic with its own source e-generator. -/
theorem y555LocalLongest_cube (i : Fin 3) :
    (y555LocalLongest i * (PresentedGroup.of (some (i, 3)) : BimonsterPresentation)) ^ 3 = 1 := by
  fin_cases i
  · exact y555LocalF1_e1_cube
  · exact y555LocalF2_e2_cube
  · exact y555LocalF3_e3_cube

/-- Each indexed longest word commutes with all original vertices except its own e-generator. -/
theorem y555LocalLongest_commute (i : Fin 3) (v : Y555Vertex) (hv : v ≠ some (i, 3)) :
    Commute (y555LocalLongest i) (PresentedGroup.of v) := by
  fin_cases i
  · exact y555LocalF1_commute v hv
  · exact y555LocalF2_commute v hv
  · exact y555LocalF3_commute v hv

/-- All three indexed actual longest words commute pairwise, including equal indices. -/
theorem y555LocalLongest_pair_commute (i j : Fin 3) :
    Commute (y555LocalLongest i) (y555LocalLongest j) := by
  fin_cases i <;> fin_cases j
  · exact Commute.refl _
  · exact y555LocalF1_commute_F2
  · exact y555LocalF3_commute_F1.symm
  · exact y555LocalF1_commute_F2.symm
  · exact Commute.refl _
  · exact y555LocalF2_commute_F3
  · exact y555LocalF3_commute_F1
  · exact y555LocalF2_commute_F3.symm
  · exact Commute.refl _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
