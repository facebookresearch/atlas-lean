/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.InfiniteWord.WordFactorComplexity

/-!
# Right-special factors of binary words

This file defines right-special factors of an infinite binary word and proves that their
number is the first difference of its factor complexity.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Right-special factors.** Let $a$ be an infinite binary word and $n$ a natural number. The
right-special factors of $a$ of length $n$ are the binary words $u$ of length $n$ such that both
$u0$ and $u1$ are factors of $a$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 5 (definition of `RS_a(n)`). -/
public def rightSpecialFactors (a : ℕ → Bool) (n : ℕ) : Set (Fin n → Bool) :=
  {u | ∀ b : Bool, (Fin.snoc (α := fun _ => Bool) u b) ∈ InfiniteWord.factorSet a (n + 1)}

/-- **The all-zero word has no right-special factors.** For every natural number $n$, the
infinite binary word $000\cdots$ has no right-special factors of length $n$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 5. -/
public theorem rightSpecialFactors_const_false (n : ℕ) :
    rightSpecialFactors (fun _ => false) n = ∅ := by
  ext u
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hu
  obtain ⟨i, hi⟩ := hu true
  have := congrFun hi (Fin.last n)
  simp at this

set_option linter.unusedVariables false in
/-- **First difference of the factor complexity of a binary word.** Let $a$ be an infinite word
over $\{0, 1\}$, let $p_a$ be its factor complexity, and let $\mathrm{RS}_a(n)$ be the set of
right-special factors of $a$ of length $n$. Then for every $n \ge 1$,
$p_a(n+1) = p_a(n) + \#\mathrm{RS}_a(n)$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 27 (`jis-2026-26.4.1-lem-27`). -/
public theorem wordFactorComplexity_succ_eq_add_rightSpecial (a : ℕ → Bool) (n : ℕ)
    (hn : 1 ≤ n) :
    wordFactorComplexity a (n + 1) =
      wordFactorComplexity a n + (rightSpecialFactors a n).ncard := by
  let append (b : Bool) (u : Fin n → Bool) := Fin.snoc (α := fun _ => Bool) u b
  let prefixes (b : Bool) := append b ⁻¹' InfiniteWord.factorSet a (n + 1)
  have hUnion : prefixes false ∪ prefixes true = InfiniteWord.factorSet a n := by
    ext u
    constructor
    · rintro (hu | hu)
      all_goals
        obtain ⟨i, hi⟩ := hu
        refine ⟨i, funext fun j => ?_⟩
        simpa only [append, Fin.snoc_castSucc, InfiniteWord.factor_apply, Fin.val_castSucc]
          using congrFun hi j.castSucc
    · rintro ⟨i, rfl⟩
      have hsnoc : append (a (i + n)) (InfiniteWord.factor a n i) =
          InfiniteWord.factor a (n + 1) i :=
        Fin.snoc_init_self (α := fun _ => Bool) (InfiniteWord.factor a (n + 1) i)
      have hm : InfiniteWord.factor a n i ∈ prefixes (a (i + n)) := ⟨i, hsnoc.symm⟩
      cases hb : a (i + n) with
      | false => exact Or.inl (hb ▸ hm)
      | true => exact Or.inr (hb ▸ hm)
  have hInter : prefixes false ∩ prefixes true = rightSpecialFactors a n := by
    ext u
    constructor
    · rintro ⟨hfalse, htrue⟩ b
      cases b
      · exact hfalse
      · exact htrue
    · intro h
      exact ⟨h false, h true⟩
  have hFactors : append false '' prefixes false ∪ append true '' prefixes true =
      InfiniteWord.factorSet a (n + 1) := by
    ext v
    constructor
    · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) <;> exact hu
    · intro hv
      have hsnoc : append (v (Fin.last n)) (Fin.init (α := fun _ => Bool) v) = v :=
        Fin.snoc_init_self v
      have hprefix : Fin.init (α := fun _ => Bool) v ∈ prefixes (v (Fin.last n)) := by
        change append (v (Fin.last n)) (Fin.init (α := fun _ => Bool) v) ∈
          InfiniteWord.factorSet a (n + 1)
        rwa [hsnoc]
      have hm : v ∈ append (v (Fin.last n)) '' prefixes (v (Fin.last n)) :=
        ⟨_, hprefix, hsnoc⟩
      cases hb : v (Fin.last n) with
      | false => exact Or.inl (hb ▸ hm)
      | true => exact Or.inr (hb ▸ hm)
  have hDisjoint : Disjoint (append false '' prefixes false) (append true '' prefixes true) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨u, _, rfl⟩ ⟨v, _, hv⟩
    exact Bool.noConfusion (Fin.snoc_inj.mp hv).2
  have hCount := Set.ncard_union_add_ncard_inter (prefixes false) (prefixes true)
  unfold wordFactorComplexity
  rw [← hFactors, Set.ncard_union_eq hDisjoint]
  rw [Set.ncard_image_of_injective _ (Fin.snoc_left_injective (α := fun _ => Bool) false),
    Set.ncard_image_of_injective _ (Fin.snoc_left_injective (α := fun _ => Bool) true)]
  rw [hUnion, hInter] at hCount
  exact hCount.symm

end

end MetaMathlibExt
