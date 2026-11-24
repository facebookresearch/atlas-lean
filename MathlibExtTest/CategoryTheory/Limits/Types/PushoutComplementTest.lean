/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Limits.Types.PushoutComplement

/-! # Original branch and empty-complement consumers -/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Limits.Types.PushoutComplementTest

/-- Both original branches and both inverse equations are retained. -/
theorem original_branches_and_inverses {A X D Z : Type u}
    {f : A ⟶ X} {g : A ⟶ D} {r : X ⟶ Z} {b : D ⟶ Z}
    (h : IsPushout f g r b) (hg : Function.Injective g) (x : X)
    (d : D) (hd : d ∉ Set.range g) :
    pushoutComplementEquiv h hg (Sum.inl x) = r x ∧
    pushoutComplementEquiv h hg (Sum.inr ⟨d, hd⟩) = b d ∧
    (pushoutComplementEquiv h hg).symm (r x) = Sum.inl x ∧
    (pushoutComplementEquiv h hg).symm (b d) = Sum.inr ⟨d, hd⟩ :=
  ⟨pushoutComplementEquiv_inl h hg x,
    pushoutComplementEquiv_inr h hg d hd,
    pushoutComplementEquiv_symm_inl h hg x,
    pushoutComplementEquiv_symm_inr h hg d hd⟩

/-- A bijective attaching leg leaves only the original old-point map. -/
theorem empty_complement_surjective_leg {A X D Z : Type u}
    {f : A ⟶ X} {g : A ⟶ D} {r : X ⟶ Z} {b : D ⟶ Z}
    (h : IsPushout f g r b) (hg : Function.Bijective g) : Function.Bijective r := by
  constructor
  · intro x y hxy
    have he : pushoutComplementEquiv h hg.1 (Sum.inl x) =
        pushoutComplementEquiv h hg.1 (Sum.inl y) := hxy
    exact Sum.inl.inj ((pushoutComplementEquiv h hg.1).injective he)
  · intro z
    obtain ⟨x, hx⟩ := (pushoutComplementEquiv h hg.1).surjective z
    rcases x with x | ⟨d, hd⟩
    · exact ⟨x, hx⟩
    · obtain ⟨a, ha⟩ := hg.2 d
      exact False.elim (hd ⟨a, ha⟩)

/-- An original complementary point never equals an old point in the supplied pushout. -/
theorem distinct_original_branches {A X D Z : Type u}
    {f : A ⟶ X} {g : A ⟶ D} {r : X ⟶ Z} {b : D ⟶ Z}
    (h : IsPushout f g r b) (hg : Function.Injective g)
    (x : X) (d : D) (hd : d ∉ Set.range g) : r x ≠ b d := by
  intro he
  have hsum : Sum.inl x = (Sum.inr ⟨d, hd⟩ : X ⊕ {d : D // d ∉ Set.range g}) :=
    (pushoutComplementEquiv h hg).injective he
  cases hsum

end CategoryTheory.Limits.Types.PushoutComplementTest
