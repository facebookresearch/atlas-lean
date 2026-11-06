/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine original C322 longest-word consequences inside independent Y444. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationY444
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationLongestWords

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The eight original C322 vertices inside the independent thirteen-generator source. -/
def y444C322Vertex : Fin 8 → Y444Vertex :=
  ![none, some (0, 0), some (0, 1), some (0, 2),
    some (1, 0), some (1, 1), some (2, 0), some (2, 1)]

/-- These local source labels embed to their exact original Y555 syntactic vertices. -/
theorem y444C322Vertex_embed (i : Fin 8) :
    y444EmbedVertex (y444C322Vertex i) = y322Vertex i := by
  revert i
  decide +kernel

/-- The eight local source vertices remain distinct. -/
theorem y444C322Vertex_injective : Function.Injective y444C322Vertex := by decide +kernel

/-- All original C322 relations hold in independent Y444, including the tenth spider power. -/
theorem y444C322Relations_valid (r : FreeGroup (Fin 8)) (hr : r ∈ y322Relations) :
    FreeGroup.lift (fun v =>
      (PresentedGroup.of (y444C322Vertex v) : Y444Presentation)) r = 1 := by
  rcases hr with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩ | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of] using y444_generator_sq (y444C322Vertex v)
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of, y444Adjacent,
      y444C322Vertex_embed] using
      y444_coxeter_relation (y444C322Vertex u) (y444C322Vertex v)
        (fun h => huv (y444C322Vertex_injective h))
  · have h := PresentedGroup.one_of_mem (rels := y444Relations)
      (show y444Spider ^ 10 ∈ y444Relations from Or.inr (Or.inr rfl))
    simpa [y322Spider, y444Spider, y444C322Vertex, map_pow, map_mul,
      FreeGroup.lift_apply_of, PresentedGroup.of, mul_assoc] using h

/-- The genuine original C322 presentation homomorphism into independent Y444. -/
def y444C322Hom : Y322Presentation →* Y444Presentation :=
  PresentedGroup.toGroup y444C322Relations_valid

/-- Every local source generator retains its exact independent-Y444 value. -/
@[simp] theorem y444C322Hom_generator (i : Fin 8) :
    y444C322Hom (PresentedGroup.of i) = PresentedGroup.of (y444C322Vertex i) :=
  PresentedGroup.toGroup.of y444C322Relations_valid

/-- The first genuine corrected longest word in independent Y444. -/
def y444LocalF1 : Y444Presentation := y444C322Hom y322CentralInvolution

/-- Exact evaluation of a finite literal local source word in independent Y444. -/
def y444LocalRestrictedWord (word : List (Fin 8)) : Y444Presentation :=
  (word.map fun i => (PresentedGroup.of (y444C322Vertex i) : Y444Presentation)).prod

/-- The first corrected spelling is the ninth power of its literal seven source letters. -/
theorem y444LocalF1_word12 :
    y444LocalF1 = y444LocalRestrictedWord y555LocalF1Support12 ^ 9 := by
  unfold y444LocalF1 y322CentralInvolution y322E7Word12
  simp only [map_pow, map_mul]
  change (y444C322Hom (PresentedGroup.of 0) * y444C322Hom (PresentedGroup.of 1) *
    y444C322Hom (PresentedGroup.of 4) * y444C322Hom (PresentedGroup.of 6) *
    y444C322Hom (PresentedGroup.of 2) * y444C322Hom (PresentedGroup.of 5) *
    y444C322Hom (PresentedGroup.of 3)) ^ 9 = _
  simp [y444LocalRestrictedWord, y555LocalF1Support12, mul_assoc]

/-- The alternative seven-letter spelling agrees by the proved original C322 consequence. -/
theorem y444LocalF1_word13 :
    y444LocalF1 = y444LocalRestrictedWord y555LocalF1Support13 ^ 9 := by
  change y444C322Hom (PresentedGroup.mk y322Relations y322E7Word12) = _
  rw [y322E7Word12_eq_word13]
  unfold y322E7Word13
  simp only [map_pow, map_mul]
  change (y444C322Hom (PresentedGroup.of 0) * y444C322Hom (PresentedGroup.of 1) *
    y444C322Hom (PresentedGroup.of 4) * y444C322Hom (PresentedGroup.of 6) *
    y444C322Hom (PresentedGroup.of 2) * y444C322Hom (PresentedGroup.of 7) *
    y444C322Hom (PresentedGroup.of 3)) ^ 9 = _
  simp [y444LocalRestrictedWord, y555LocalF1Support13, mul_assoc]

/-- The actual source longest word is an involution in independent Y444. -/
theorem y444LocalF1_square : y444LocalF1 * y444LocalF1 = 1 := by
  simpa only [y444LocalF1, map_mul, map_one] using
    congrArg y444C322Hom y322CentralInvolution_square

/-- Exact nonadjacent source involutions commute by their original Coxeter relation. -/
theorem y444Source_generator_commute (u v : Y444Vertex) (ha : ¬ y444Adjacent u v) :
    Commute (PresentedGroup.of u : Y444Presentation) (PresentedGroup.of v) := by
  by_cases heq : u = v
  · subst v
    exact Commute.refl _
  have hu : (PresentedGroup.of u : Y444Presentation)⁻¹ = PresentedGroup.of u :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using y444_generator_sq u)
  have hv : (PresentedGroup.of v : Y444Presentation)⁻¹ = PresentedGroup.of v :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using y444_generator_sq v)
  have h := y444_coxeter_relation u v heq
  have h2 : ((PresentedGroup.of u : Y444Presentation) * PresentedGroup.of v) *
      (PresentedGroup.of u * PresentedGroup.of v) = 1 := by
    simpa only [ite_eq_right ha, pow_two] using h
  have hi := eq_inv_of_mul_eq_one_left h2
  exact (by simpa only [mul_inv_rev, hu, hv] using hi :
    (PresentedGroup.of u : Y444Presentation) * PresentedGroup.of v =
      PresentedGroup.of v * PresentedGroup.of u)

/-- A literal local source word commutes with a vertex nonadjacent to all its letters. -/
theorem y444LocalRestrictedWord_commute (word : List (Fin 8)) (v : Y444Vertex)
    (h : ∀ i ∈ word, ¬ y444Adjacent (y444C322Vertex i) v) :
    Commute (y444LocalRestrictedWord word) (PresentedGroup.of v) := by
  induction word with
  | nil => exact Commute.one_left _
  | cons i word ih =>
    have hi := y444Source_generator_commute (y444C322Vertex i) v (h i (by simp))
    have ht := ih (fun j hj => h j (by simp [hj]))
    simpa only [y444LocalRestrictedWord, List.map_cons, List.prod_cons] using hi.mul_left ht

/-- Every independent source vertex except e1 is local or avoids one corrected support. -/
theorem y444LocalF1_vertex_coverage (v : Y444Vertex) (hv : v ≠ some (0, 3)) :
    (∃ i : Fin 8, y444C322Vertex i = v) ∨
      (∀ i ∈ y555LocalF1Support12, ¬ y444Adjacent (y444C322Vertex i) v) ∨
      (∀ i ∈ y555LocalF1Support13, ¬ y444Adjacent (y444C322Vertex i) v) := by
  revert v
  decide +kernel

/-- The genuine longest word commutes with every independent source vertex except e1. -/
theorem y444LocalF1_commute (v : Y444Vertex) (hv : v ≠ some (0, 3)) :
    Commute y444LocalF1 (PresentedGroup.of v) := by
  rcases y444LocalF1_vertex_coverage v hv with ⟨i, rfl⟩ | h | h
  · have hc := congrArg y444C322Hom
      (y322CentralInvolution_commute (PresentedGroup.of i))
    change y444LocalF1 * PresentedGroup.of (y444C322Vertex i) =
      PresentedGroup.of (y444C322Vertex i) * y444LocalF1
    simpa only [map_mul, y444LocalF1, y444C322Hom_generator] using hc
  · rw [y444LocalF1_word12]
    exact (y444LocalRestrictedWord_commute _ v h).pow_left 9
  · rw [y444LocalF1_word13]
    exact (y444LocalRestrictedWord_commute _ v h).pow_left 9

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
