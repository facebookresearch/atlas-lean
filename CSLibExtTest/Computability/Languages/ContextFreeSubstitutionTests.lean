/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Substitution
public import CSLibExt.Computability.Languages.ContextFree.Closure

/-!
# Tests for substitution of context-free languages

* Substituting `{[0], [1, 1]}` for `true` in `{[true, true]}` gives a context-free language,
  which contains `[0, 1, 1]` and not `[0, 1]`.
* Substituting the language of all words over `{0}` (context-free, by `IsContextFree.kstar`)
  for every letter.
* `substitution_letter`, `substitution_mul` and the closure theorem instantiated.
-/

@[expose] public section

namespace Cslib.Language.ContextFreeSubstitutionTests

/-- `true ↦ {[0], [1, 1]}`, `false ↦ {[]}`. -/
def s : Bool → Language ℕ
  | true => {[0]} + {[1, 1]}
  | false => 1

theorem s_isContextFree : ∀ b, (s b).IsContextFree
  | true => IsContextFree.add (IsContextFree.singleton_word _) (IsContextFree.singleton_word _)
  | false => IsContextFree.one

example : (substitution ({[true, true]} : Language Bool) s).IsContextFree :=
  IsContextFree.substitution (IsContextFree.singleton_word _) s_isContextFree

example : [0, 1, 1] ∈ substitution ({[true, true]} : Language Bool) s := by
  refine ⟨[true, true], rfl, ?_⟩
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact Language.mem_mul.2 ⟨[0], Or.inl rfl, [1, 1], Or.inr rfl, rfl⟩

example : [0, 1] ∉ substitution ({[true, true]} : Language Bool) s := by
  rintro ⟨x, hx, hy⟩
  rw [Set.mem_singleton_iff.1 hx] at hy
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hy
  obtain ⟨u, hu, v, hv, huv⟩ := Language.mem_mul.1 hy
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp at huv

example (L : Language Bool) (hL : L.IsContextFree) :
    (substitution L fun _ => KStar.kstar ({[0]} : Language ℕ)).IsContextFree :=
  IsContextFree.substitution hL fun _ => IsContextFree.kstar (IsContextFree.singleton_word _)

example (a : Bool) : substitution ({[a]} : Language Bool) s = s a := substitution_letter a s

example : substitution ({[true]} * {[false]} : Language Bool) s =
    substitution {[true]} s * substitution {[false]} s :=
  substitution_mul _ _ s

example : substitution ({[true]} * {[false]} : Language Bool) s = s true * s false := by
  rw [substitution_mul, substitution_letter, substitution_letter]

end Cslib.Language.ContextFreeSubstitutionTests
