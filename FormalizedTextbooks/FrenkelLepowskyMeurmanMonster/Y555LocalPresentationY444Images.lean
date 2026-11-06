/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact images of all sixteen original Y555 generators in independent Y444. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationY444Interactions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTerminalImages

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Original nonterminal vertices retain their exact source labels; terminals use longest words. -/
def y444Y555Image : Y555Vertex → Y444Presentation
  | none => PresentedGroup.of none
  | some (i, k) => match k with
    | 0 => PresentedGroup.of (some (i, 0))
    | 1 => PresentedGroup.of (some (i, 1))
    | 2 => PresentedGroup.of (some (i, 2))
    | 3 => PresentedGroup.of (some (i, 3))
    | _ => y444LocalLongest i

/-- Every embedded original nonterminal has exactly its independent source-generator image. -/
@[simp] theorem y444Y555Image_embed (v : Y444Vertex) :
    y444Y555Image (y444EmbedVertex v) = PresentedGroup.of v := by
  cases v with
  | none => rfl
  | some p => rcases p with ⟨i, k⟩; fin_cases k <;> rfl

/-- Every original terminal has exactly its own corrected longest-word image. -/
@[simp] theorem y444Y555Image_terminal (i : Fin 3) :
    y444Y555Image (some (i, 4)) = y444LocalLongest i := rfl

/-- Every original source vertex is an exact nonterminal inclusion or one terminal vertex. -/
theorem y444Y555_vertex_cases (v : Y555Vertex) :
    (∃ w : Y444Vertex, y444EmbedVertex w = v) ∨ (∃ i : Fin 3, v = some (i, 4)) := by
  revert v
  decide +kernel

/-- Every actual image satisfies the original generator's defining square relation. -/
theorem y444Y555Image_square (v : Y555Vertex) : y444Y555Image v ^ 2 = 1 := by
  rcases y444Y555_vertex_cases v with ⟨w, rfl⟩ | ⟨i, rfl⟩
  · rw [y444Y555Image_embed]
    exact y444_generator_sq w
  · simpa only [y444Y555Image_terminal, pow_two] using y444LocalLongest_square i

/-- Every terminal-image pair has the precise exponent required by the original source tree. -/
theorem y444Y555Image_terminal_pair (i : Fin 3) (v : Y555Vertex) :
    (y444LocalLongest i * y444Y555Image v) ^
      (if y555Adjacent (some (i, 4)) v then 3 else 2 : ℕ) = 1 := by
  by_cases he : v = some (i, 3)
  · subst v
    simpa only [y555Adjacent_terminal, ite_true, y444Y555Image] using y444LocalLongest_cube i
  · have ha : ¬ y555Adjacent (some (i, 4)) v :=
      fun h => he ((y555Adjacent_terminal i v).mp h)
    rw [ite_eq_right ha]
    apply y555Source_commuting_square
    · rcases y444Y555_vertex_cases v with ⟨w, rfl⟩ | ⟨j, rfl⟩
      · rw [y444Y555Image_embed]
        apply y444LocalLongest_commute
        intro hw
        apply he
        rw [hw]
        rfl
      · rw [y444Y555Image_terminal]
        exact y444LocalLongest_pair_commute i j
    · simpa only [pow_two] using y444LocalLongest_square i
    · exact y444Y555Image_square v

/-- Every distinct original Coxeter pair holds for the exact independent-Y444 source images. -/
theorem y444Y555Image_coxeter (u v : Y555Vertex) (huv : u ≠ v) :
    (y444Y555Image u * y444Y555Image v) ^
      (if y555Adjacent u v then 3 else 2 : ℕ) = 1 := by
  rcases y444Y555_vertex_cases u with ⟨a, rfl⟩ | ⟨i, rfl⟩
  · rcases y444Y555_vertex_cases v with ⟨b, rfl⟩ | ⟨j, rfl⟩
    · rw [y444Y555Image_embed, y444Y555Image_embed]
      exact y444_coxeter_relation a b (fun h => huv (congrArg y444EmbedVertex h))
    · have h := y444Y555Image_terminal_pair j (y444EmbedVertex a)
      simp only [y555Source_adjacent_symm (some (j, 4)) (y444EmbedVertex a)] at h
      by_cases ha : y555Adjacent (y444EmbedVertex a) (some (j, 4))
      · simp only [ite_eq_left ha] at h ⊢
        have hr := congrArg (MulAut.conj (y444LocalLongest j)⁻¹) h
        simpa [map_pow, map_one, MulAut.conj_apply, mul_assoc] using hr
      · simp only [ite_eq_right ha] at h ⊢
        have hr := congrArg (MulAut.conj (y444LocalLongest j)⁻¹) h
        simpa [map_pow, map_one, MulAut.conj_apply, mul_assoc] using hr
  · rw [y444Y555Image_terminal]
    exact y444Y555Image_terminal_pair i v

/-- Every literal original Y555 relator holds in the independently presented Y444 group. -/
theorem y444Y555Image_relations (r : FreeGroup Y555Vertex) (hr : r ∈ y555Relations) :
    FreeGroup.lift y444Y555Image r = 1 := by
  rcases hr with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩ | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of] using y444Y555Image_square v
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of] using
      y444Y555Image_coxeter u v huv
  · have h := PresentedGroup.one_of_mem (rels := y444Relations)
      (show y444Spider ^ 10 ∈ y444Relations from Or.inr (Or.inr rfl))
    simpa [y555Spider, y444Spider, y444Y555Image, map_pow, map_mul,
      FreeGroup.lift_apply_of, PresentedGroup.of, mul_assoc] using h

/-- The genuine original-source homomorphism from independent Y555 to independent Y444. -/
def y555IntoY444 : BimonsterPresentation →* Y444Presentation :=
  PresentedGroup.toGroup y444Y555Image_relations

/-- Every original defining generator retains its exact declared independent-Y444 image. -/
@[simp] theorem y555IntoY444_generator (v : Y555Vertex) :
    y555IntoY444 (PresentedGroup.of v) = y444Y555Image v :=
  PresentedGroup.toGroup.of y444Y555Image_relations

/-- The source inclusion followed by longest-word substitution fixes every Y444 element. -/
theorem y555IntoY444_comp_inclusion :
    y555IntoY444.comp y444IntoY555 = MonoidHom.id Y444Presentation := by
  apply PresentedGroup.ext
  intro v
  simp only [MonoidHom.comp_apply, y444IntoY555_generator, y555IntoY444_generator,
    y444Y555Image_embed, MonoidHom.id_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
