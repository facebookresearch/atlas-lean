/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthTrace
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPriorTraces
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthTrace

/-! The actual ninth representative belongs to none of the eight prior local orbit families. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- No actual signed-short axis can be transported locally to the ninth candidate. -/
theorem generatedNinth_not_local_short (h : H) (r : GriessShortIndex) (c : ZMod 2) :
    rhoLocal h (conwayShortAxis r c) ≠ generatedNinthAxis := by
  intro he
  have ht := generatedFourth_matrix_square_trace_local h (conwayShortAxis r c)
  rw [he, generatedNinth_matrix_square_trace, generatedFourth_matrix_square_trace_short] at ht
  norm_num at ht

/-- No actual octad-image axis can be transported locally to the ninth candidate. -/
theorem generatedNinth_not_local_octad (h : H) (o : Fin 759) (e : Fin 64) (c : ZMod 2) :
    rhoLocal h (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)) ≠ generatedNinthAxis := by
  intro he
  have ht := generatedFourth_matrix_square_trace_local h
    (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))
  rw [he, generatedNinth_matrix_square_trace, generatedFourth_matrix_square_trace_octad] at ht
  norm_num at ht

/-- No actual odd-image axis can be transported locally to the ninth candidate. -/
theorem generatedNinth_not_local_odd (h : H) (d : Fin 2048) (i : Fin 24) (c : ZMod 2) :
    rhoLocal h (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) c)) ≠ generatedNinthAxis := by
  intro he
  have ht := generatedFourth_matrix_square_trace_local h
    (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) c))
  rw [he, generatedNinth_matrix_square_trace, generatedFourth_matrix_square_trace_odd] at ht
  norm_num at ht

/-- No actual fourth-orbit axis can be transported locally to the ninth candidate. -/
theorem generatedNinth_not_local_fourth (h : H) :
    rhoLocal h generatedFourthAxis ≠ generatedNinthAxis := by
  intro he
  have ht := generatedFourth_matrix_square_trace_local h generatedFourthAxis
  rw [he, generatedNinth_matrix_square_trace, generatedFourth_matrix_square_trace] at ht
  norm_num at ht


/-- No actual fifth-orbit axis can be transported locally to the ninth candidate. -/
theorem generatedNinth_not_local_fifth (h : H) :
    rhoLocal h generatedFifthAxis ≠ generatedNinthAxis := by
  intro he
  have ht := generatedFourth_matrix_square_trace_local h generatedFifthAxis
  rw [he, generatedNinth_matrix_square_trace, generatedFifth_matrix_square_trace] at ht
  norm_num at ht

/-- No actual sixth-orbit axis can be transported locally to the ninth candidate. -/
theorem generatedNinth_not_local_sixth (h : H) :
    rhoLocal h generatedSixthAxis ≠ generatedNinthAxis := by
  intro he
  have ht := generatedFourth_matrix_square_trace_local h generatedSixthAxis
  rw [he, generatedNinth_matrix_square_trace, generatedNinth_prior_sixth_trace] at ht
  norm_num at ht

/-- No actual seventh-orbit axis can be transported locally to the ninth candidate. -/
theorem generatedNinth_not_local_seventh (h : H) :
    rhoLocal h generatedSeventhAxis ≠ generatedNinthAxis := by
  intro he
  have ht := generatedFourth_matrix_square_trace_local h generatedSeventhAxis
  rw [he, generatedNinth_matrix_square_trace, generatedNinth_prior_seventh_trace] at ht
  norm_num at ht

/-- No actual eighth-orbit axis can be transported locally to the ninth candidate. -/
theorem generatedNinth_not_local_eighth (h : H) :
    rhoLocal h generatedEighthAxis ≠ generatedNinthAxis := by
  intro he
  have ht := generatedFourth_matrix_square_trace_local h generatedEighthAxis
  rw [he, generatedNinth_matrix_square_trace, generatedNinth_prior_eighth_trace] at ht
  norm_num at ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
