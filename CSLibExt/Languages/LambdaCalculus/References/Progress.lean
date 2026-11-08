/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The simply typed lambda calculus with references: progress
-/
module

public import CSLibExt.Languages.LambdaCalculus.References.Typing
public import CSLibExt.Languages.LambdaCalculus.References.Semantics

/-!
# Progress

Pierce, *Types and Programming Languages*, Theorem 13.5.7: a closed,
well-typed term is either a value or can take an evaluation step in any store
that is well typed with respect to the same store typing.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.References

universe u

variable {Base : Type u}

/-- Progress (TAPL Theorem 13.5.7): if `∅ | S ⊢ t : T` and `∅ | S ⊢ μ`, then
`t` is a value or `t | μ → t' | μ'` for some `t'` and `μ'`. -/
theorem progress {S : List (Ty Base)} {μ : Store Base} {t : Term Base} {T : Ty Base}
    (ht : HasType [] S t T) (hμ : StoreTyped [] S μ) :
    t.Value ∨ ∃ t' μ', Step t μ t' μ' := by
  generalize hΓ : ([] : List (Ty Base)) = Γ at ht
  induction ht with
  | var hx =>
      subst hΓ
      simp at hx
  | lam _ _ => exact .inl (.lam _ _)
  | app hf _ ihf iha =>
      rcases ihf hμ hΓ with hvf | ⟨f', μ', hf'⟩
      · obtain ⟨body, rfl⟩ := hf.lam_of_value hvf
        rcases iha hμ hΓ with hva | ⟨a', μ', ha'⟩
        · exact .inr ⟨_, _, .appAbs hva⟩
        · exact .inr ⟨_, _, .appRight hvf ha'⟩
      · exact .inr ⟨_, _, .appLeft hf'⟩
  | unit => exact .inl .unit
  | loc _ => exact .inl (.loc _)
  | ref _ ih =>
      rcases ih hμ hΓ with hv | ⟨t', μ', ht'⟩
      · exact .inr ⟨_, _, .refValue hv⟩
      · exact .inr ⟨_, _, .ref ht'⟩
  | deref ht ih =>
      rcases ih hμ hΓ with hv | ⟨t', μ', ht'⟩
      · obtain ⟨l, rfl, hl⟩ := ht.loc_of_value hv
        obtain ⟨v, hlv, _, _⟩ := hμ.exists_of_getElem? hl
        exact .inr ⟨_, _, .derefLoc hlv⟩
      · exact .inr ⟨_, _, .deref ht'⟩
  | assign ht₁ _ ih₁ ih₂ =>
      rcases ih₁ hμ hΓ with hv₁ | ⟨t₁', μ', ht₁'⟩
      · obtain ⟨l, rfl, hl⟩ := ht₁.loc_of_value hv₁
        rcases ih₂ hμ hΓ with hv₂ | ⟨t₂', μ', ht₂'⟩
        · have hlt : l < μ.length := by
            rw [hμ.length_eq]
            exact (List.getElem?_eq_some_iff.mp hl).1
          exact .inr ⟨_, _, .assignLoc hv₂ hlt⟩
        · exact .inr ⟨_, _, .assignRight hv₁ ht₂'⟩
      · exact .inr ⟨_, _, .assignLeft ht₁'⟩

end Cslib.Languages.LambdaCalculus.References
