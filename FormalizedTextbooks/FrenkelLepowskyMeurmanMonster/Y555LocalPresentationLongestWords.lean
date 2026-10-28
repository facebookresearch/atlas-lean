/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine longest-word consequences inside independent Y555.
Source: L.H. Soicher, Cambridge PhD thesis (1985), printed p.51,
DOI 10.17863/CAM.110463. The further C431 cubic relation is not assumed. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationFijEquality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3CentralProduct

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Nonadjacent source Y555 involutions commute by their actual defining relations. -/
theorem y555Source_generator_commute (u v : Y555Vertex) (ha : ¬ y555Adjacent u v) :
    Commute (PresentedGroup.of u : BimonsterPresentation) (PresentedGroup.of v) := by
  by_cases heq : u = v
  · subst v
    exact Commute.refl _
  have hu : (PresentedGroup.of u : BimonsterPresentation)⁻¹ = PresentedGroup.of u :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using y555_generator_sq u)
  have hv : (PresentedGroup.of v : BimonsterPresentation)⁻¹ = PresentedGroup.of v :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using y555_generator_sq v)
  have h := y555_coxeter_relation u v heq
  have h2 : ((PresentedGroup.of u : BimonsterPresentation) * PresentedGroup.of v) *
      (PresentedGroup.of u * PresentedGroup.of v) = 1 := by
    simpa only [ite_eq_right ha, pow_two] using h
  have hi := eq_inv_of_mul_eq_one_left h2
  exact (by simpa only [mul_inv_rev, hu, hv] using hi :
    (PresentedGroup.of u : BimonsterPresentation) * PresentedGroup.of v =
      PresentedGroup.of v * PresentedGroup.of u)

/-- The first corrected longest involution inside the original independent Y555 group. -/
def y555LocalF1 : BimonsterPresentation := y322IntoY555 y322CentralInvolution

/-- Literal seven-generator support for the first corrected longest-word spelling. -/
def y555LocalF1Support12 : List (Fin 8) := [0, 1, 4, 6, 2, 5, 3]

/-- Literal support of its equal alternative spelling, omitting the second arm's c-generator. -/
def y555LocalF1Support13 : List (Fin 8) := [0, 1, 4, 6, 2, 7, 3]

/-- Evaluation of a literal restricted source word in the independent Y555 group. -/
def y555LocalRestrictedWord (word : List (Fin 8)) : BimonsterPresentation :=
  (word.map fun i => (PresentedGroup.of (y322Vertex i) : BimonsterPresentation)).prod

/-- The first spelling is the ninth power of its exact seven source vertices. -/
theorem y555LocalF1_word12 :
    y555LocalF1 = y555LocalRestrictedWord y555LocalF1Support12 ^ 9 := by
  unfold y555LocalF1 y322CentralInvolution y322E7Word12
  simp only [map_pow, map_mul]
  change (y322IntoY555 (PresentedGroup.of 0) * y322IntoY555 (PresentedGroup.of 1) *
    y322IntoY555 (PresentedGroup.of 4) * y322IntoY555 (PresentedGroup.of 6) *
    y322IntoY555 (PresentedGroup.of 2) * y322IntoY555 (PresentedGroup.of 5) *
    y322IntoY555 (PresentedGroup.of 3)) ^ 9 = _
  simp [y555LocalRestrictedWord, y555LocalF1Support12, mul_assoc]

/-- The second spelling is the ninth power of its equal exact alternative source support. -/
theorem y555LocalF1_word13 :
    y555LocalF1 = y555LocalRestrictedWord y555LocalF1Support13 ^ 9 := by
  change y322IntoY555 (PresentedGroup.mk y322Relations y322E7Word12) = _
  rw [y322E7Word12_eq_word13_in_Y555]
  unfold y322E7Word13
  simp only [map_pow, map_mul]
  change (y322IntoY555 (PresentedGroup.of 0) * y322IntoY555 (PresentedGroup.of 1) *
    y322IntoY555 (PresentedGroup.of 4) * y322IntoY555 (PresentedGroup.of 6) *
    y322IntoY555 (PresentedGroup.of 2) * y322IntoY555 (PresentedGroup.of 7) *
    y322IntoY555 (PresentedGroup.of 3)) ^ 9 = _
  simp [y555LocalRestrictedWord, y555LocalF1Support13, mul_assoc]

/-- Any restricted word whose letters are nonadjacent to a vertex commutes with that vertex. -/
theorem y555LocalRestrictedWord_commute (word : List (Fin 8)) (v : Y555Vertex)
    (h : ∀ i ∈ word, ¬ y555Adjacent (y322Vertex i) v) :
    Commute (y555LocalRestrictedWord word) (PresentedGroup.of v) := by
  induction word with
  | nil => exact Commute.one_left _
  | cons i word ih =>
    have hi := y555Source_generator_commute (y322Vertex i) v (h i (by simp))
    have ht := ih (fun j hj => h j (by simp [hj]))
    simpa only [y555LocalRestrictedWord, List.map_cons, List.prod_cons] using hi.mul_left ht

/-- Every vertex except e1 lies locally or is nonadjacent to one of the two exact word supports. -/
theorem y555LocalF1_vertex_coverage (v : Y555Vertex) (hv : v ≠ some (0, 3)) :
    (∃ i : Fin 8, y322Vertex i = v) ∨
      (∀ i ∈ y555LocalF1Support12, ¬ y555Adjacent (y322Vertex i) v) ∨
      (∀ i ∈ y555LocalF1Support13, ¬ y555Adjacent (y322Vertex i) v) := by
  revert v
  decide +kernel

/-- The actual longest involution commutes with every original source generator except e1. -/
theorem y555LocalF1_commute (v : Y555Vertex) (hv : v ≠ some (0, 3)) :
    Commute y555LocalF1 (PresentedGroup.of v) := by
  rcases y555LocalF1_vertex_coverage v hv with ⟨i, rfl⟩ | h | h
  · have hc := congrArg y322IntoY555
      (y322CentralInvolution_commute (PresentedGroup.of i))
    change y555LocalF1 * PresentedGroup.of (y322Vertex i) =
      PresentedGroup.of (y322Vertex i) * y555LocalF1
    simpa only [map_mul, y555LocalF1, y322IntoY555_generator] using hc
  · rw [y555LocalF1_word12]
    exact (y555LocalRestrictedWord_commute _ v h).pow_left 9
  · rw [y555LocalF1_word13]
    exact (y555LocalRestrictedWord_commute _ v h).pow_left 9

/-- The actual longest source word remains an involution under the genuine restricted map. -/
theorem y555LocalF1_square : y555LocalF1 * y555LocalF1 = 1 := by
  simpa only [y555LocalF1, map_mul, map_one] using
    congrArg y322IntoY555 y322CentralInvolution_square

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
