/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-! # A supplied Type pushout as old points and complement

The original pushout maps define a bijection from old points and the complement
of an injective attaching leg. Both branches and their inverse equations retain
the supplied square. This shares the private Type proof formerly used by
`SSet.labelledFreeFiller.degreewiseEquiv`; the scalar public definitions and
forward equations remain unchanged.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Limits.Types

/-- A supplied Type pushout along an injective leg is old points plus its complement. -/
def pushoutComplementEquiv {A X D Z : Type u}
    {f : A ⟶ X} {g : A ⟶ D} {r : X ⟶ Z} {b : D ⟶ Z}
    (h : IsPushout f g r b) (hg : Function.Injective g) :
    (X ⊕ {d : D // d ∉ Set.range g}) ≃ Z := by
  classical
  let complementRight (d : D) : X ⊕ {d : D // d ∉ Set.range g} :=
    if h : d ∈ Set.range g then
      Sum.inl (f ((Equiv.ofInjective g hg).symm ⟨d, h⟩))
    else Sum.inr ⟨d, h⟩
  have complementRight_image (a : A) : complementRight (g a) = Sum.inl (f a) := by
    simp [complementRight]
  let right : D ⟶ (X ⊕ {d : D // d ∉ Set.range g}) :=
    ↾(complementRight)
  have compat : f ≫ (↾Sum.inl) = g ≫ right := by
    ext a
    exact (complementRight_image a).symm
  let normal := h.desc (↾Sum.inl) right compat
  let forward : (X ⊕ {d : D // d ∉ Set.range g}) → Z :=
    Sum.elim r (fun d => b d.val)
  have normal_old (x : X) : normal (r x) = Sum.inl x :=
    ConcreteCategory.congr_hom (h.inl_desc (↾Sum.inl) right compat) x
  have normal_cell (d : D) : normal (b d) = complementRight d :=
    ConcreteCategory.congr_hom (h.inr_desc (↾Sum.inl) right compat) d
  have cell_forward (d : D) : forward (complementRight d) = b d := by
    by_cases hd : d ∈ Set.range g
    · dsimp [complementRight, forward]
      rw [dite_eq_left hd]
      have w := ConcreteCategory.congr_hom h.w ((Equiv.ofInjective g hg).symm ⟨d, hd⟩)
      simpa only [Sum.elim_inl, types_comp_apply, Equiv.apply_ofInjective_symm] using w
    · simp only [complementRight, dite_eq_right hd, forward, Sum.elim_inr]
  refine ⟨forward, normal, ?_, ?_⟩
  · rintro (x | d)
    · exact normal_old x
    · change normal (b d.val) = Sum.inr d
      rw [normal_cell]
      simp only [complementRight, dite_eq_right d.property]
  · intro z
    obtain ⟨x, rfl⟩ | ⟨d, rfl⟩ := eq_or_eq_of_isPushout h z
    · rw [normal_old]
      rfl
    · rw [normal_cell, cell_forward]


variable {A X D Z : Type u} {f : A ⟶ X} {g : A ⟶ D} {r : X ⟶ Z} {b : D ⟶ Z}

/-- The old branch is the original pushout map. -/
lemma pushoutComplementEquiv_inl (h : IsPushout f g r b) (hg : Function.Injective g)
    (x : X) : pushoutComplementEquiv h hg (Sum.inl x) = r x := rfl

/-- The complementary branch is the original second pushout map. -/
lemma pushoutComplementEquiv_inr (h : IsPushout f g r b) (hg : Function.Injective g)
    (d : D) (hd : d ∉ Set.range g) :
    pushoutComplementEquiv h hg (Sum.inr ⟨d, hd⟩) = b d := rfl

/-- The inverse retains every original old point. -/
lemma pushoutComplementEquiv_symm_inl (h : IsPushout f g r b)
    (hg : Function.Injective g) (x : X) :
    (pushoutComplementEquiv h hg).symm (r x) = Sum.inl x := by
  apply (pushoutComplementEquiv h hg).injective
  rw [Equiv.apply_symm_apply, pushoutComplementEquiv_inl]

/-- The inverse retains every original complementary point. -/
lemma pushoutComplementEquiv_symm_inr (h : IsPushout f g r b)
    (hg : Function.Injective g) (d : D) (hd : d ∉ Set.range g) :
    (pushoutComplementEquiv h hg).symm (b d) = Sum.inr ⟨d, hd⟩ := by
  apply (pushoutComplementEquiv h hg).injective
  rw [Equiv.apply_symm_apply, pushoutComplementEquiv_inr]

/-- The forward function uses exactly the original two pushout maps. -/
lemma pushoutComplementEquiv_coe (h : IsPushout f g r b) (hg : Function.Injective g) :
    (pushoutComplementEquiv h hg : X ⊕ {d : D // d ∉ Set.range g} → Z) =
      Sum.elim r (fun d => b d.val) := rfl

/-- Equality of pushout images reflects equality of an original point outside
the injective attaching leg, using the canonical complement equivalence. -/
theorem outside_inl_injective {S X Y P : Type u} {f : S ⟶ X} {g : S ⟶ Y}
    {i : X ⟶ P} {j : Y ⟶ P} (h : IsPushout f g i j) [Mono f]
    (x y : X) (hx : ¬ ∃ a, f a = x) (he : i x = i y) : x = y := by
  classical
  have hfi : Function.Injective f := injective_of_mono f
  let E := pushoutComplementEquiv h.flip hfi
  have hy : y ∉ Set.range f := by
    rintro ⟨a, rfl⟩
    have H : (Sum.inr ⟨x, hx⟩ : Y ⊕ {x : X // x ∉ Set.range f}) = Sum.inl (g a) := by
      calc
        _ = E.symm (i x) := (pushoutComplementEquiv_symm_inr h.flip hfi x hx).symm
        _ = E.symm (j (g a)) := congrArg E.symm (he.trans (ConcreteCategory.congr_hom h.w a))
        _ = _ := pushoutComplementEquiv_symm_inl h.flip hfi (g a)
    cases H
  have H : (Sum.inr ⟨x, hx⟩ : Y ⊕ {x : X // x ∉ Set.range f}) = Sum.inr ⟨y, hy⟩ := by
    apply E.injective
    exact he
  exact congrArg Subtype.val (Sum.inr.inj H)

end CategoryTheory.Limits.Types
