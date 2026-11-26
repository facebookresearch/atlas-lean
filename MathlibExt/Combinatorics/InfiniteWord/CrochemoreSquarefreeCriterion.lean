/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.InfiniteWord.SquareFreeWord

import Mathlib.Tactic

/-!
# Crochemore's finite test for squarefree morphisms over the ternary alphabet

Wishlist record of Crochemore's length-5 criterion: a morphism defined on the
free monoid over the ternary alphabet preserves squarefreeness on all words
exactly when it preserves squarefreeness on squarefree words of length at most 5.

Provenance: Max Crochemore, "Sharp characterizations of squarefree morphisms,"
Theoretical Computer Science 18(2) (1982), 221-226,
DOI 10.1016/0304-3975(82)90023-8; secondary statement in James D. Currie,
"Finite Test Sets for Morphisms That Are Squarefree on Some of Thue's Squarefree
Ternary Words," Journal of Integer Sequences 22 (2019), Article 19.8.2,
authoritative source
`https://cs.uwaterloo.ca/journals/JIS/VOL22/Currie/currie20.tex`,
lines 85-100 (line 100 attributes the length-5 criterion to Crochemore),
file SHA-256
`37d67fb53bb5168db23faf3c9a436709c2f09b7045201e42e1f07fff43f27c46`,
span SHA-256
`ae0ba8107ccc5dfcd1a4065609be8a31f1a809ea3f1f9b37ce7a2cd762dd5bf9`.
-/

@[expose] public section

namespace MetaMathlibExt

private theorem croch_squarefree_of_length_le_three {α : Type*} (w : List α)
    (hlen : w.length ≤ 3) (hadj : ∀ a, ¬ [a, a].IsInfix w) : IsSquareFreeWord w := by
  intro s hs hsq
  obtain ⟨x, hx, rfl⟩ := hsq
  have hxpos : 0 < x.length := List.length_pos_iff.mpr hx
  have hxx : (x ++ x).length ≤ 3 := le_trans hs.length_le hlen
  have hxlen : x.length = 1 := by
    simp only [List.length_append] at hxx
    omega
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hxlen
  exact hadj a (by simpa using hs)

private theorem croch_squarefree_singleton {α : Type*} (a : α) :
    IsSquareFreeWord [a] := by
  apply croch_squarefree_of_length_le_three [a] (by simp)
  intro d hd
  simp only [List.infix_cons_iff] at hd
  aesop

private theorem croch_squarefree_pair {α : Type*} {a b : α} (hab : a ≠ b) :
    IsSquareFreeWord [a, b] := by
  apply croch_squarefree_of_length_le_three [a, b] (by simp)
  intro d hd
  simp only [List.infix_cons_iff] at hd
  aesop

private theorem croch_squarefree_triple {α : Type*} {a b c : α}
    (hab : a ≠ b) (hbc : b ≠ c) : IsSquareFreeWord [a, b, c] := by
  apply croch_squarefree_of_length_le_three [a, b, c] (by simp)
  intro d hd
  simp only [List.infix_cons_iff] at hd
  aesop

private theorem croch_not_squarefree_of_square_infix {α : Type*} {w x : List α}
    (hx : x ≠ []) (hxx : (x ++ x).IsInfix w) : ¬ IsSquareFreeWord w := by
  intro hw
  exact hw (x ++ x) hxx ⟨x, hx, rfl⟩

private theorem croch_four_avoiding_pattern :
    ∀ x a b c d : TernaryAlphabet, x ≠ a → x ≠ b → x ≠ c → x ≠ d →
      a = b ∨ b = c ∨ c = d ∨ (a = c ∧ b = d) := by
  decide

private theorem croch_length_le_three_of_squarefree_not_mem (x : TernaryAlphabet)
    (w : List TernaryAlphabet) (hw : IsSquareFreeWord w) (hx : x ∉ w) : w.length ≤ 3 := by
  match w with
  | [] | [_] | [_, _] | [_, _, _] => simp
  | a :: b :: c :: d :: r =>
    exfalso
    have h4 : IsSquareFreeWord [a, b, c, d] := hw.of_isInfix ⟨[], r, by simp⟩
    simp only [List.mem_cons, not_or] at hx
    have hne : x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d :=
      ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩
    rcases croch_four_avoiding_pattern x a b c d hne.1 hne.2.1 hne.2.2.1 hne.2.2.2 with
      hab | hbc | hcd | ⟨hac, hbd⟩
    · subst b
      exact h4 [a, a] ⟨[], [c, d], by simp⟩ ⟨[a], by simp, rfl⟩
    · subst c
      exact h4 [b, b] ⟨[a], [d], by simp⟩ ⟨[b], by simp, rfl⟩
    · subst d
      exact h4 [c, c] ⟨[a, b], [], by simp⟩ ⟨[c], by simp, rfl⟩
    · subst c
      subst d
      exact h4 [a, b, a, b] List.infix_rfl ⟨[a, b], by simp, rfl⟩

private theorem croch_at_most_three {T : Type*} (f : TernaryAlphabet → List T)
    (hne : ∀ a, f a ≠ []) {x : TernaryAlphabet} {w : List TernaryAlphabet}
    (hw : IsSquareFreeWord w) (hin : (w.flatMap f).IsInfix (f x)) : w.length ≤ 3 := by
  by_cases hx : x ∈ w
  · obtain ⟨l, r, rfl⟩ := List.mem_iff_append.mp hx
    have hback : (f x).IsInfix ((l ++ x :: r).flatMap f) := by
      exact ⟨l.flatMap f, r.flatMap f, by simp⟩
    have heq : (l ++ x :: r).flatMap f = f x := List.infix_antisymm hin hback
    have hlen := congrArg List.length heq
    simp only [List.flatMap_append, List.flatMap_cons, List.length_append] at hlen
    have hl : (l.flatMap f).length = 0 := by omega
    have hr : (r.flatMap f).length = 0 := by omega
    have hlnil : l.flatMap f = [] := List.length_eq_zero_iff.mp hl
    have hrnil : r.flatMap f = [] := List.length_eq_zero_iff.mp hr
    have lnil : l = [] := by
      cases l with
      | nil => rfl
      | cons a l => exact (hne a ((List.flatMap_eq_nil_iff.mp hlnil) a (by simp))).elim
    have rnil : r = [] := by
      cases r with
      | nil => rfl
      | cons a r => exact (hne a ((List.flatMap_eq_nil_iff.mp hrnil) a (by simp))).elim
    simp [lnil, rnil]
  · exact croch_length_le_three_of_squarefree_not_mem x w hw hx

private theorem croch_empty_or_nonempty {T : Type*} (f : TernaryAlphabet → List T)
    (htest : ∀ w : List TernaryAlphabet, w.length ≤ 5 →
      IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f)) :
    (∀ a, f a = []) ∨ ∀ a, f a ≠ [] := by
  classical
  by_cases hall : ∀ a, f a = []
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨b, hb⟩ := hall
    intro a ha
    have hab : a ≠ b := by
      intro hab
      exact hb (hab ▸ ha)
    have hout := htest [b, a, b] (by simp)
      (croch_squarefree_triple hab.symm hab)
    simp only [List.flatMap_cons, List.flatMap_nil, ha, List.append_nil] at hout
    exact hout (f b ++ f b) List.infix_rfl ⟨f b, hb, rfl⟩

private theorem croch_letter_image_squarefree {T : Type*}
    (f : TernaryAlphabet → List T)
    (htest : ∀ w : List TernaryAlphabet, w.length ≤ 5 →
      IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f)) (a : TernaryAlphabet) :
    IsSquareFreeWord (f a) := by
  simpa using htest [a] (by simp) (croch_squarefree_singleton a)

private theorem croch_eq_of_image_prefix {T : Type*}
    (f : TernaryAlphabet → List T) (hne : ∀ a, f a ≠ [])
    (htest : ∀ w : List TernaryAlphabet, w.length ≤ 5 →
      IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f))
    {a b : TernaryAlphabet} (hp : (f a).IsPrefix (f b)) : a = b := by
  by_contra hab
  obtain ⟨r, hr⟩ := hp
  have hout := htest [a, b] (by simp) (croch_squarefree_pair hab)
  have hsq : (f a ++ f a).IsInfix ([a, b].flatMap f) :=
    ⟨[], r, by simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.nil_append, List.append_assoc, hr]⟩
  exact hout (f a ++ f a) hsq ⟨f a, hne a, rfl⟩

private theorem croch_eq_of_image_suffix {T : Type*}
    (f : TernaryAlphabet → List T) (hne : ∀ a, f a ≠ [])
    (htest : ∀ w : List TernaryAlphabet, w.length ≤ 5 →
      IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f))
    {a b : TernaryAlphabet} (hs : (f a).IsSuffix (f b)) : a = b := by
  by_contra hab
  obtain ⟨l, hl⟩ := hs
  have hba : b ≠ a := fun hba => hab hba.symm
  have hout := htest [b, a] (by simp) (croch_squarefree_pair hba)
  have hsq : (f a ++ f a).IsInfix ([b, a].flatMap f) :=
    ⟨l, [], by
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [← List.append_assoc, hl]⟩
  exact hout (f a ++ f a) hsq ⟨f a, hne a, rfl⟩

private theorem croch_no_suffix_overlap {T : Type*}
    (f : TernaryAlphabet → List T)
    (htest : ∀ w : List TernaryAlphabet, w.length ≤ 5 →
      IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f))
    {z β γ : TernaryAlphabet} {p : List T} (hzβ : z ≠ β) (hpne : p ≠ [])
    (hp : p.IsPrefix (f β)) (hs : (f z ++ p).IsSuffix (f γ)) : False := by
  obtain ⟨l, hl⟩ := hs
  obtain ⟨r, hr⟩ := hp
  by_cases hγβ : γ = β
  · subst γ
    have hβz : β ≠ z := fun h => hzβ h.symm
    have hout := htest [β, z, β] (by simp) (croch_squarefree_triple hβz hzβ)
    apply hout ((f z ++ p) ++ (f z ++ p))
    · refine ⟨l, r, ?_⟩
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      calc
        l ++ ((f z ++ p) ++ (f z ++ p)) ++ r =
            (l ++ (f z ++ p)) ++ (f z ++ (p ++ r)) := by simp [List.append_assoc]
        _ = f β ++ (f z ++ f β) := by rw [hl, hr]
    · exact ⟨f z ++ p, by simp [hpne], rfl⟩
  · have hout := htest [γ, β] (by simp) (croch_squarefree_pair hγβ)
    apply hout (p ++ p)
    · refine ⟨l ++ f z, r, ?_⟩
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      calc
        (l ++ f z) ++ (p ++ p) ++ r = (l ++ (f z ++ p)) ++ (p ++ r) := by
          simp [List.append_assoc]
        _ = f γ ++ f β := by rw [hl, hr]
    · exact ⟨p, hpne, rfl⟩

private theorem croch_no_prefix_overlap {T : Type*}
    (f : TernaryAlphabet → List T)
    (htest : ∀ w : List TernaryAlphabet, w.length ≤ 5 →
      IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f))
    {α z γ : TernaryAlphabet} {s : List T} (hαz : α ≠ z) (hsne : s ≠ [])
    (hs : s.IsSuffix (f α)) (hp : (s ++ f z).IsPrefix (f γ)) : False := by
  obtain ⟨l, hl⟩ := hs
  obtain ⟨r, hr⟩ := hp
  by_cases hαγ : α = γ
  · subst γ
    have hzα : z ≠ α := fun h => hαz h.symm
    have hout := htest [α, z, α] (by simp) (croch_squarefree_triple hαz hzα)
    apply hout ((s ++ f z) ++ (s ++ f z))
    · refine ⟨l, r, ?_⟩
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      calc
        l ++ ((s ++ f z) ++ (s ++ f z)) ++ r =
            (l ++ s) ++ (f z ++ ((s ++ f z) ++ r)) := by simp [List.append_assoc]
        _ = f α ++ (f z ++ f α) := by rw [hl, hr]
    · exact ⟨s ++ f z, by simp [hsne], rfl⟩
  · have hout := htest [α, γ] (by simp) (croch_squarefree_pair hαγ)
    apply hout (s ++ s)
    · refine ⟨l, f z ++ r, ?_⟩
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      calc
        l ++ (s ++ s) ++ (f z ++ r) = (l ++ s) ++ ((s ++ f z) ++ r) := by
          simp [List.append_assoc]
        _ = f α ++ f γ := by rw [hl, hr]
    · exact ⟨s, hsne, rfl⟩

private theorem croch_no_image_overlap {T : Type*}
    (f : TernaryAlphabet → List T)
    (htest : ∀ w : List TernaryAlphabet, w.length ≤ 5 →
      IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f))
    {a b : TernaryAlphabet} {s : List T} (hab : a ≠ b) (hsne : s ≠ [])
    (hsa : s.IsSuffix (f a)) (hsb : s.IsPrefix (f b)) : False := by
  obtain ⟨l, hl⟩ := hsa
  obtain ⟨r, hr⟩ := hsb
  have hout := htest [a, b] (by simp) (croch_squarefree_pair hab)
  apply hout (s ++ s)
  · refine ⟨l, r, ?_⟩
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [← List.append_assoc, hl, List.append_assoc, hr]
  · exact ⟨s, hsne, rfl⟩

private theorem croch_suffix_factor {T : Type*} {p q x : List T}
    (hp : p.IsSuffix x) (hq : q.IsSuffix x) (hlen : p.length ≤ q.length) :
    ∃ d, q = d ++ p := by
  obtain ⟨u, hu⟩ := hp
  obtain ⟨v, hv⟩ := hq
  have heq : u ++ p = v ++ q := hu.trans hv.symm
  rcases List.append_eq_append_iff.mp heq with ⟨d, huv, hq'⟩ | ⟨d, hvu, hp'⟩
  · have hdlen := congrArg List.length hq'
    simp only [List.length_append] at hdlen
    have : d = [] := List.length_eq_zero_iff.mp (by omega)
    subst d
    exact ⟨[], by simpa using hq'.symm⟩
  · exact ⟨d, hp'⟩

private theorem croch_prefix_factor {T : Type*} {p q x : List T}
    (hp : p.IsPrefix x) (hq : q.IsPrefix x) (hlen : p.length ≤ q.length) :
    ∃ d, q = p ++ d := by
  obtain ⟨u, hu⟩ := hp
  obtain ⟨v, hv⟩ := hq
  have heq : p ++ u = q ++ v := hu.trans hv.symm
  rcases List.append_eq_append_iff.mp heq with ⟨d, hpq, -⟩ | ⟨d, hqp, hp'⟩
  · exact ⟨d, hpq⟩
  · have hdlen := congrArg List.length hqp
    simp only [List.length_append] at hdlen
    have : d = [] := List.length_eq_zero_iff.mp (by omega)
    subst d
    exact ⟨[], by simpa using hqp.symm⟩

private theorem croch_prefix_parse {A T : Type*} (g : A → List T)
    (hne : ∀ a, g a ≠ []) (hinj : ∀ {a b}, (g a).IsPrefix (g b) → a = b)
    {a b : A} {U V : List A} {p q : List T}
    (hp : p.IsPrefix (g a)) (hq : q.IsPrefix (g b))
    (heq : U.flatMap g ++ p = V.flatMap g ++ q) :
    (U = V ∧ p = q) ∨
      (V = U ++ [a] ∧ p = g a ∧ q = []) ∨
      (U = V ++ [b] ∧ p = [] ∧ q = g b) := by
  induction U generalizing V with
  | nil =>
    cases V with
    | nil => exact Or.inl ⟨rfl, by simpa using heq⟩
    | cons z V =>
      simp only [List.flatMap_nil, List.nil_append, List.flatMap_cons,
        List.append_assoc] at heq
      have hza : z = a := by
        apply hinj
        apply List.IsPrefix.trans (l₂ := p) _ hp
        exact ⟨V.flatMap g ++ q, heq.symm⟩
      subst z
      have hlen := congrArg List.length heq
      simp only [List.length_append] at hlen
      have hplen : p.length = (g a).length := by
        have := hp.length_le
        omega
      have hpa : p = g a := hp.eq_of_length hplen
      have htail : V.flatMap g = [] := by
        apply List.length_eq_zero_iff.mp
        omega
      have hV : V = [] := by
        cases V with
        | nil => rfl
        | cons z V => exact (hne z ((List.flatMap_eq_nil_iff.mp htail) z (by simp))).elim
      subst V
      simp only [List.flatMap_nil, List.nil_append, hpa] at heq
      right
      left
      exact ⟨by simp, hpa, (List.append_left_inj (g a)).mp (by simpa using heq.symm)⟩
  | cons z U ih =>
    cases V with
    | nil =>
      simp only [List.flatMap_cons, List.flatMap_nil, List.nil_append,
        List.append_assoc] at heq
      have hzb : z = b := by
        apply hinj
        apply List.IsPrefix.trans (l₂ := q) _ hq
        exact ⟨U.flatMap g ++ p, heq⟩
      subst z
      have hlen := congrArg List.length heq
      simp only [List.length_append] at hlen
      have hqlen : q.length = (g b).length := by
        have := hq.length_le
        omega
      have hqb : q = g b := hq.eq_of_length hqlen
      have htail : U.flatMap g = [] := by
        apply List.length_eq_zero_iff.mp
        omega
      have hU : U = [] := by
        cases U with
        | nil => rfl
        | cons z U => exact (hne z ((List.flatMap_eq_nil_iff.mp htail) z (by simp))).elim
      subst U
      simp only [List.flatMap_nil, hqb] at heq
      right
      right
      exact ⟨by simp, (List.append_left_inj (g b)).mp (by simpa using heq), hqb⟩
    | cons y V =>
      simp only [List.flatMap_cons, List.append_assoc] at heq
      have hzy : z = y := by
        rcases List.append_eq_append_iff.mp heq with ⟨d, h, -⟩ | ⟨d, h, -⟩
        · exact hinj ⟨d, h.symm⟩
        · exact (hinj ⟨d, h.symm⟩).symm
      subst y
      have htail : U.flatMap g ++ p = V.flatMap g ++ q :=
        (List.append_right_inj (g z)).mp heq
      rcases ih (V := V) htail with hsame | hextra | hextra
      · exact Or.inl ⟨by simp [hsame.1], hsame.2⟩
      · right
        left
        exact ⟨by simp [hextra.1], hextra.2⟩
      · right
        right
        exact ⟨by simp [hextra.1], hextra.2⟩

private theorem croch_suffix_parse {T : Type*} (f : TernaryAlphabet → List T)
    (hne : ∀ a, f a ≠ [])
    (hsuffix : ∀ {a b}, (f a).IsSuffix (f b) → a = b)
    {a b : TernaryAlphabet} {U V : List TernaryAlphabet} {A S : List T}
    (hA : A.IsSuffix (f a)) (hS : S.IsSuffix (f b))
    (heq : A ++ U.flatMap f = S ++ V.flatMap f) :
    (U = V ∧ A = S) ∨
      (V = a :: U ∧ A = f a ∧ S = []) ∨
      (U = b :: V ∧ A = [] ∧ S = f b) := by
  let g : TernaryAlphabet → List T := fun z => (f z).reverse
  have hgne : ∀ z, g z ≠ [] := by
    intro z hz
    apply hne z
    simpa [g] using congrArg List.reverse hz
  have hginj : ∀ {x y}, (g x).IsPrefix (g y) → x = y := by
    intro x y h
    apply hsuffix
    obtain ⟨r, hr⟩ := h
    refine ⟨r.reverse, ?_⟩
    simpa [g] using congrArg List.reverse hr
  have hp : A.reverse.IsPrefix (g a) := by
    obtain ⟨r, hr⟩ := hA
    refine ⟨r.reverse, ?_⟩
    simpa [g] using congrArg List.reverse hr
  have hq : S.reverse.IsPrefix (g b) := by
    obtain ⟨r, hr⟩ := hS
    refine ⟨r.reverse, ?_⟩
    simpa [g] using congrArg List.reverse hr
  have heq' : U.reverse.flatMap g ++ A.reverse =
      V.reverse.flatMap g ++ S.reverse := by
    simpa only [List.reverse_append, List.reverse_flatMap, g, Function.comp_def] using
      congrArg List.reverse heq
  rcases croch_prefix_parse g hgne hginj hp hq heq' with hsame | hextra | hextra
  · left
    exact ⟨by simpa using congrArg List.reverse hsame.1,
      by simpa using congrArg List.reverse hsame.2⟩
  · right
    left
    exact ⟨by simpa using congrArg List.reverse hextra.1,
      by simpa [g] using congrArg List.reverse hextra.2.1,
      by simpa using congrArg List.reverse hextra.2.2⟩
  · right
    right
    exact ⟨by simpa using congrArg List.reverse hextra.1,
      by simpa using congrArg List.reverse hextra.2.1,
      by simpa [g] using congrArg List.reverse hextra.2.2⟩

private theorem croch_prefix_cover {A T : Type*} (f : A → List T)
    (hne : ∀ a, f a ≠ []) {z : List T} (hz : z ≠ []) {w : List A}
    (hp : z.IsPrefix (w.flatMap f)) :
    ∃ l a r p s, w = l ++ a :: r ∧ f a = p ++ s ∧
      z = l.flatMap f ++ p ∧ p ≠ [] := by
  induction w generalizing z with
  | nil =>
    obtain ⟨q, hq⟩ := hp
    simp only [List.flatMap_nil, List.append_eq_nil_iff] at hq
    exact (hz hq.1).elim
  | cons a w ih =>
    obtain ⟨q, hq⟩ := hp
    simp only [List.flatMap_cons] at hq
    rcases List.append_eq_append_iff.mp hq with ⟨s, hfa, -⟩ | ⟨t, hzt, htail⟩
    · exact ⟨[], a, w, z, s, by simp, hfa, by simp, hz⟩
    · by_cases ht : t = []
      · subst t
        simp only [List.append_nil] at hzt
        exact ⟨[], a, w, f a, [], by simp, by simp, hzt, hne a⟩
      · obtain ⟨l, b, r, p, s, hw, hfb, htp, hpne⟩ :=
          ih ht ⟨q, htail.symm⟩
        refine ⟨a :: l, b, r, p, s, ?_, hfb, ?_, hpne⟩
        · simp [hw]
        · rw [hzt, htp]
          simp [List.append_assoc]

private theorem croch_prefix_cover_or_tail {A T : Type*} (f : A → List T)
    (hne : ∀ a, f a ≠ []) {z : List T} (hz : z ≠ []) (w : List A) (C : List T)
    (hp : z.IsPrefix (w.flatMap f ++ C)) :
    (∃ l a r p s, w = l ++ a :: r ∧ f a = p ++ s ∧
      z = l.flatMap f ++ p ∧ p ≠ []) ∨
      ∃ p s, C = p ++ s ∧ z = w.flatMap f ++ p ∧ p ≠ [] := by
  induction w generalizing z with
  | nil =>
    obtain ⟨q, hq⟩ := hp
    right
    exact ⟨z, q, by simpa using hq.symm, by simp, hz⟩
  | cons a w ih =>
    obtain ⟨q, hq⟩ := hp
    simp only [List.flatMap_cons, List.append_assoc] at hq
    rcases List.append_eq_append_iff.mp hq with ⟨s, hfa, -⟩ | ⟨t, hzt, htail⟩
    · left
      exact ⟨[], a, w, z, s, by simp, hfa, by simp, hz⟩
    · by_cases ht : t = []
      · subst t
        simp only [List.append_nil] at hzt
        left
        exact ⟨[], a, w, f a, [], by simp, by simp, hzt, hne a⟩
      · rcases ih ht ⟨q, htail.symm⟩ with
          ⟨l, b, r, p, s, hw, hfb, htp, hpne⟩ | ⟨p, s, hC, htp, hpne⟩
        · left
          refine ⟨a :: l, b, r, p, s, ?_, hfb, ?_, hpne⟩
          · simp [hw]
          · rw [hzt, htp]
            simp [List.append_assoc]
        · right
          refine ⟨p, s, hC, ?_, hpne⟩
          rw [hzt, htp]
          simp [List.append_assoc]

private theorem croch_proper_prefix_cut_or_tail {A T : Type*} (f : A → List T)
    (w : List A) (C : List T) {z q : List T} (hq : q ≠ [])
    (hcut : z ++ q = w.flatMap f ++ C) :
    (∃ l a r p s, w = l ++ a :: r ∧ f a = p ++ s ∧
      z = l.flatMap f ++ p ∧ s ≠ []) ∨
      ∃ p s, C = p ++ s ∧ z = w.flatMap f ++ p ∧ s ≠ [] := by
  induction w generalizing z q with
  | nil =>
    right
    exact ⟨z, q, by simpa using hcut.symm, by simp, hq⟩
  | cons a w ih =>
    simp only [List.flatMap_cons, List.append_assoc] at hcut
    rcases List.append_eq_append_iff.mp hcut with ⟨d, hfa, hqtail⟩ |
      ⟨t, hzt, htail⟩
    · by_cases hd : d = []
      · subst d
        simp only [List.append_nil] at hfa hqtail
        rcases ih (z := []) hq (by simpa using hqtail) with
            ⟨l, b, r, p, s, hw, hfb, htp, hsne⟩ |
            ⟨p, s, hC, htp, hsne⟩
        · left
          refine ⟨a :: l, b, r, p, s, ?_, hfb, ?_, hsne⟩
          · simp [hw]
          · calc
              z = f a := hfa.symm
              _ = f a ++ [] := by simp
              _ = f a ++ (l.flatMap f ++ p) := by rw [htp]
              _ = (a :: l).flatMap f ++ p := by simp [List.append_assoc]
        · right
          refine ⟨p, s, hC, ?_, hsne⟩
          calc
            z = f a := hfa.symm
            _ = f a ++ [] := by simp
            _ = f a ++ (w.flatMap f ++ p) := by rw [htp]
            _ = (a :: w).flatMap f ++ p := by simp [List.append_assoc]
      · left
        exact ⟨[], a, w, z, d, by simp, hfa, by simp, hd⟩
    · rcases ih hq htail.symm with
        ⟨l, b, r, p, s, hw, hfb, htp, hsne⟩ |
        ⟨p, s, hC, htp, hsne⟩
      · left
        refine ⟨a :: l, b, r, p, s, ?_, hfb, ?_, hsne⟩
        · simp [hw]
        · rw [hzt, htp]
          simp [List.append_assoc]
      · right
        refine ⟨p, s, hC, ?_, hsne⟩
        rw [hzt, htp]
        simp [List.append_assoc]

private theorem croch_suffix_cover {A T : Type*} (f : A → List T)
    (hne : ∀ a, f a ≠ []) {z : List T} (hz : z ≠ []) {w : List A}
    (hs : z.IsSuffix (w.flatMap f)) :
    ∃ l a r p s, w = l ++ a :: r ∧ f a = p ++ s ∧
      z = s ++ r.flatMap f ∧ s ≠ [] := by
  let g : A → List T := fun a => (f a).reverse
  have hgne : ∀ a, g a ≠ [] := by
    intro a ha
    exact hne a (by simpa [g] using congrArg List.reverse ha)
  obtain ⟨q, hq⟩ := hs
  have hp : z.reverse.IsPrefix (w.reverse.flatMap g) := by
    refine ⟨q.reverse, ?_⟩
    simpa only [List.reverse_append, List.reverse_flatMap, g, Function.comp_def] using
      congrArg List.reverse hq
  have hzrev : z.reverse ≠ [] := by simpa using hz
  obtain ⟨l, a, r, p, s, hw, hfa, hzp, hpne⟩ :=
    croch_prefix_cover g hgne hzrev hp
  refine ⟨r.reverse, a, l.reverse, s.reverse, p.reverse, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg List.reverse hw
  · simpa [g] using congrArg List.reverse hfa
  · simpa only [List.reverse_append, List.reverse_reverse, List.reverse_flatMap, g,
      Function.comp_def] using congrArg List.reverse hzp
  · simpa using hpne

private theorem croch_square_cover {T : Type*} (f : TernaryAlphabet → List T)
    (hne : ∀ a, f a ≠ [])
    (htest : ∀ w : List TernaryAlphabet, w.length ≤ 5 →
      IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f))
    {w : List TernaryAlphabet} {x : List T} (hx : x ≠ [])
    (hxx : (x ++ x).IsInfix (w.flatMap f)) :
    ∃ pre a mid c post pa A C sc,
      w = pre ++ a :: (mid ++ c :: post) ∧ f a = pa ++ A ∧ f c = C ++ sc ∧
        x ++ x = A ++ mid.flatMap f ++ C ∧ A ≠ [] ∧ C ≠ [] := by
  obtain ⟨u, v, huv⟩ := hxx
  have hz : x ++ x ++ v ≠ [] := by simp [hx]
  have hs : (x ++ x ++ v).IsSuffix (w.flatMap f) :=
    ⟨u, by simpa [List.append_assoc] using huv⟩
  obtain ⟨pre, a, r, pa, A, hw, hfa, htail, hA⟩ :=
    croch_suffix_cover f hne hz hs
  rcases List.append_eq_append_iff.mp htail with ⟨d, hAd, -⟩ | ⟨z, hxxz, hr⟩
  · have hin : (x ++ x).IsInfix (f a) :=
      ⟨pa, d, by rw [hfa, hAd]; simp [List.append_assoc]⟩
    exact (croch_not_squarefree_of_square_infix hx hin
      (croch_letter_image_squarefree f htest a)).elim
  · by_cases hz0 : z = []
    · subst z
      simp only [List.append_nil] at hxxz
      have hin : (x ++ x).IsInfix (f a) := ⟨pa, [], by simp [hfa, hxxz]⟩
      exact (croch_not_squarefree_of_square_infix hx hin
        (croch_letter_image_squarefree f htest a)).elim
    · obtain ⟨mid, c, post, C, sc, hrword, hfc, hzcover, hC⟩ :=
        croch_prefix_cover f hne hz0 ⟨v, hr.symm⟩
      refine ⟨pre, a, mid, c, post, pa, A, C, sc, ?_, hfa, hfc, ?_, hA, hC⟩
      · rw [hw, hrword]
      · rw [hxxz, hzcover]
        simp [List.append_assoc]

private theorem croch_middle_length {T : Type*} (f : TernaryAlphabet → List T)
    (htest : ∀ w : List TernaryAlphabet, w.length ≤ 5 →
      IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f))
    {a c : TernaryAlphabet} {mid : List TernaryAlphabet}
    {pa A C sc x : List T} (hx : x ≠ []) (hq : IsSquareFreeWord (a :: mid ++ [c]))
    (hfa : f a = pa ++ A) (hfc : f c = C ++ sc)
    (hxx : x ++ x = A ++ mid.flatMap f ++ C) : 4 ≤ mid.length := by
  by_contra hlen
  have hle : (a :: mid ++ [c]).length ≤ 5 := by simp; omega
  have hout := htest (a :: mid ++ [c]) hle hq
  have hin : (x ++ x).IsInfix ((a :: mid ++ [c]).flatMap f) := by
    refine ⟨pa, sc, ?_⟩
    simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.append_nil]
    rw [hfa, hfc, hxx]
    simp [List.append_assoc]
  exact croch_not_squarefree_of_square_infix hx hin hout

private theorem croch_midpoint_cover {T : Type*} (f : TernaryAlphabet → List T)
    (hne : ∀ a, f a ≠ [])
    {a c : TernaryAlphabet} {mid : List TernaryAlphabet}
    {pa A C sc x : List T} (hx : x ≠ []) (hq : IsSquareFreeWord (a :: mid ++ [c]))
    (hmidlen : 4 ≤ mid.length) (hfa : f a = pa ++ A) (hfc : f c = C ++ sc)
    (hxx : x ++ x = A ++ mid.flatMap f ++ C) :
    ∃ U b V P S, mid = U ++ b :: V ∧ f b = P ++ S ∧
      x = A ++ U.flatMap f ++ P ∧ x = S ++ V.flatMap f ++ C ∧ S ≠ [] := by
  have hmid : IsSquareFreeWord mid := hq.of_isInfix ⟨[a], [c], by simp⟩
  have hxx' : x ++ x = A ++ (mid.flatMap f ++ C) := by
    simpa [List.append_assoc] using hxx
  rcases List.append_eq_append_iff.mp hxx' with ⟨d, hAx, hxrest⟩ |
    ⟨z, hxA, hrest⟩
  · have hmx : (mid.flatMap f).IsInfix x :=
      ⟨d, C, by simpa [List.append_assoc] using hxrest.symm⟩
    have hxa : x.IsInfix (f a) :=
      ⟨pa, d, by rw [hfa, hAx]; simp [List.append_assoc]⟩
    have hle := croch_at_most_three f hne hmid (hmx.trans hxa)
    omega
  · by_cases hz : z = []
    · subst z
      simp only [List.append_nil, List.nil_append] at hxA hrest
      have hmx : (mid.flatMap f).IsInfix x := ⟨[], C, by simpa using hrest⟩
      have hxa : x.IsInfix (f a) := ⟨pa, [], by simp [hfa, hxA]⟩
      have hle := croch_at_most_three f hne hmid (hmx.trans hxa)
      omega
    · rcases croch_proper_prefix_cut_or_tail f mid C hx hrest.symm with
        ⟨U, b, V, P, S, hmidword, hfb, hzcut, hSne⟩ |
        ⟨P, S, hC, hzcut, hSne⟩
      · refine ⟨U, b, V, P, S, hmidword, hfb, ?_, ?_, hSne⟩
        · rw [hxA, hzcut]
          simp [List.append_assoc]
        · have heq : (U.flatMap f ++ P) ++ (S ++ V.flatMap f ++ C) =
              (U.flatMap f ++ P) ++ x := by
            calc
              (U.flatMap f ++ P) ++ (S ++ V.flatMap f ++ C) =
                  mid.flatMap f ++ C := by
                    rw [hmidword]
                    simp only [List.flatMap_append, List.flatMap_cons]
                    rw [hfb]
                    simp [List.append_assoc]
              _ = z ++ x := hrest
              _ = (U.flatMap f ++ P) ++ x := by rw [hzcut]
          exact ((List.append_right_inj (U.flatMap f ++ P)).mp heq).symm
      · have heq : (mid.flatMap f ++ P) ++ S = (mid.flatMap f ++ P) ++ x := by
          calc
            (mid.flatMap f ++ P) ++ S = mid.flatMap f ++ C := by
              rw [hC]
              simp [List.append_assoc]
            _ = z ++ x := hrest
            _ = (mid.flatMap f ++ P) ++ x := by rw [hzcut]
        have hSx : S = x := (List.append_right_inj (mid.flatMap f ++ P)).mp heq
        have hmx : (mid.flatMap f).IsInfix x :=
          ⟨A, P, by rw [hxA, hzcut]; simp [List.append_assoc]⟩
        have hxc : x.IsInfix (f c) :=
          ⟨P, sc, by rw [hfc, hC, hSx]⟩
        have hle := croch_at_most_three f hne hmid (hmx.trans hxc)
        omega

private theorem croch_ne_of_pair_infix {α : Type*} {a b : α} {w : List α}
    (hw : IsSquareFreeWord w) (hab : [a, b].IsInfix w) : a ≠ b := by
  intro h
  subst b
  exact hw [a, a] hab ⟨[a], by simp, rfl⟩

private theorem croch_endpoint_bounds {T : Type*} (f : TernaryAlphabet → List T)
    (htest : ∀ w : List TernaryAlphabet, w.length ≤ 5 →
      IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f))
    {a b c : TernaryAlphabet} {U V : List TernaryAlphabet}
    {pa A P S C sc x : List T} (hq : IsSquareFreeWord (a :: U ++ b :: V ++ [c]))
    (hlen : 3 ≤ U.length + V.length) (hfa : f a = pa ++ A) (hfb : f b = P ++ S)
    (hfc : f c = C ++ sc) (hx₁ : x = A ++ U.flatMap f ++ P)
    (hx₂ : x = S ++ V.flatMap f ++ C) :
    S.length + P.length ≤ x.length ∧ A.length + C.length ≤ x.length := by
  have hx₁len := congrArg List.length hx₁
  have hx₂len := congrArg List.length hx₂
  simp only [List.length_append] at hx₁len hx₂len
  constructor
  · by_contra hbound
    have hshort : (A ++ U.flatMap f).length < S.length := by
      simp only [List.length_append]
      omega
    have heq : (A ++ U.flatMap f) ++ P = S ++ (V.flatMap f ++ C) := by
      calc
        (A ++ U.flatMap f) ++ P = x := hx₁.symm
        _ = S ++ (V.flatMap f ++ C) := by simpa [List.append_assoc] using hx₂
    rcases List.append_eq_append_iff.mp heq with ⟨d, hS, hP⟩ | ⟨d, hAU, -⟩
    · have hd : d ≠ [] := by
        apply List.length_pos_iff.mp
        have hdlen := congrArg List.length hS
        simp only [List.length_append] at hdlen
        omega
      by_cases hU : U = []
      · subst U
        have hV : V ≠ [] := by intro h; subst V; simp at hlen
        cases V with
        | nil => exact (hV rfl).elim
        | cons z V =>
          have hbz : b ≠ z := croch_ne_of_pair_infix hq ⟨[a], V ++ [c], by simp⟩
          have hds : d.IsSuffix (f b) := by
            apply List.IsSuffix.trans (l₂ := S)
            · exact ⟨A, by simpa using hS.symm⟩
            · exact ⟨P, hfb.symm⟩
          have hdp : (d ++ f z).IsPrefix (f b) := by
            refine ⟨V.flatMap f ++ C ++ S, ?_⟩
            rw [hfb, hP]
            simp [List.append_assoc]
          exact croch_no_prefix_overlap f htest hbz hd hds hdp
      · let z := U.getLast hU
        have hflat : U.flatMap f = U.dropLast.flatMap f ++ f z := by
          rw [← List.dropLast_append_getLast hU]
          simp [z]
        have hzb : z ≠ b := by
          apply croch_ne_of_pair_infix hq
          refine ⟨a :: U.dropLast, V ++ [c], ?_⟩
          rw [← List.dropLast_append_getLast hU]
          simp [z, List.append_assoc]
        have hdp : d.IsPrefix (f b) := by
          refine ⟨(V.flatMap f ++ C) ++ S, ?_⟩
          rw [hfb, hP]
          simp [List.append_assoc]
        have hzds : (f z ++ d).IsSuffix (f b) := by
          apply List.IsSuffix.trans (l₂ := S)
          · refine ⟨A ++ U.dropLast.flatMap f, ?_⟩
            rw [hS, hflat]
            simp [List.append_assoc]
          · exact ⟨P, hfb.symm⟩
        exact croch_no_suffix_overlap f htest hzb hd hdp hzds
    · have hlen' := congrArg List.length hAU
      simp only [List.length_append] at hlen'
      omega
  · by_contra hbound
    have hshort : (S ++ V.flatMap f).length < A.length := by
      simp only [List.length_append]
      omega
    have heq : A ++ (U.flatMap f ++ P) = (S ++ V.flatMap f) ++ C := by
      calc
        A ++ (U.flatMap f ++ P) = x := by simpa [List.append_assoc] using hx₁.symm
        _ = (S ++ V.flatMap f) ++ C := hx₂
    rcases List.append_eq_append_iff.mp heq with ⟨d, hSV, -⟩ | ⟨d, hA, hC⟩
    · have hlen' := congrArg List.length hSV
      simp only [List.length_append] at hlen'
      omega
    · have hd : d ≠ [] := by
        apply List.length_pos_iff.mp
        have hdlen := congrArg List.length hA
        simp only [List.length_append] at hdlen
        omega
      by_cases hV : V = []
      · subst V
        have hU : U ≠ [] := by intro h; subst U; simp at hlen
        cases U with
        | nil => exact (hU rfl).elim
        | cons z U =>
          have haz : a ≠ z := croch_ne_of_pair_infix hq ⟨[], U ++ b :: [c], by simp⟩
          have hds : d.IsSuffix (f a) := by
            apply List.IsSuffix.trans (l₂ := A)
            · exact ⟨S, by simpa using hA.symm⟩
            · exact ⟨pa, hfa.symm⟩
          have hdp : (d ++ f z).IsPrefix (f c) := by
            refine ⟨U.flatMap f ++ P ++ sc, ?_⟩
            rw [hfc, hC]
            simp [List.append_assoc]
          exact croch_no_prefix_overlap f htest haz hd hds hdp
      · let z := V.getLast hV
        have hflat : V.flatMap f = V.dropLast.flatMap f ++ f z := by
          rw [← List.dropLast_append_getLast hV]
          simp [z]
        have hzc : z ≠ c := by
          apply croch_ne_of_pair_infix hq
          refine ⟨a :: U ++ b :: V.dropLast, [], ?_⟩
          rw [← List.dropLast_append_getLast hV]
          simp [z, List.append_assoc]
        have hdp : d.IsPrefix (f c) := by
          refine ⟨(U.flatMap f ++ P) ++ sc, ?_⟩
          rw [hfc, hC]
          simp [List.append_assoc]
        have hzds : (f z ++ d).IsSuffix (f a) := by
          apply List.IsSuffix.trans (l₂ := A)
          · refine ⟨S ++ V.dropLast.flatMap f, ?_⟩
            rw [hA, hflat]
            simp [List.append_assoc]
          · exact ⟨pa, hfa.symm⟩
        exact croch_no_suffix_overlap f htest hzc hd hdp hzds

private theorem croch_midpoint_cover_prefix {T : Type*}
    (f : TernaryAlphabet → List T) (hne : ∀ a, f a ≠ [])
    (htest : ∀ w : List TernaryAlphabet, w.length ≤ 5 →
      IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f))
    {a c : TernaryAlphabet} {mid : List TernaryAlphabet}
    {pa A C sc x : List T} (hx : x ≠ []) (hC : C ≠ [])
    (hq : IsSquareFreeWord (a :: mid ++ [c])) (hmidlen : 4 ≤ mid.length)
    (hfa : f a = pa ++ A) (hfc : f c = C ++ sc)
    (hxx : x ++ x = A ++ mid.flatMap f ++ C) :
    ∃ U b V P S, mid = U ++ b :: V ∧ f b = P ++ S ∧
      x = A ++ U.flatMap f ++ P ∧ x = S ++ V.flatMap f ++ C ∧ P ≠ [] := by
  obtain ⟨U, b, V, P, S, hmid, hfb, hx₁, hx₂, hSne⟩ :=
    croch_midpoint_cover f hne hx hq hmidlen hfa hfc hxx
  by_cases hP : P = []
  · subst P
    simp only [List.append_nil] at hfb hx₁
    by_cases hU : U = []
    · subst U
      simp only [List.flatMap_nil, List.append_nil] at hx₁
      simp only [List.nil_append] at hmid
      have hlen : 3 ≤ V.length := by
        have hmidlen' := hmidlen
        rw [hmid] at hmidlen'
        simp only [List.length_cons] at hmidlen'
        omega
      have hq' : IsSquareFreeWord (a :: [] ++ b :: V ++ [c]) := by
        simpa [hmid] using hq
      have hbound := (croch_endpoint_bounds f htest hq' (by simpa using hlen)
        hfa hfb hfc (by simpa using hx₁) hx₂).2
      have hxlen := congrArg List.length hx₁
      have : C = [] := List.length_eq_zero_iff.mp (by omega)
      exact (hC this).elim
    · let z := U.getLast hU
      have hflat : U.flatMap f = U.dropLast.flatMap f ++ f z := by
        rw [← List.dropLast_append_getLast hU]
        simp [z]
      refine ⟨U.dropLast, z, b :: V, f z, [], ?_, by simp, ?_, ?_, hne z⟩
      · rw [hmid, ← List.dropLast_append_getLast hU]
        simp [z, List.append_assoc]
      · rw [hx₁, hflat]
        simp [List.append_assoc]
      · simpa [List.flatMap_cons, hfb, List.append_assoc] using hx₂
  · exact ⟨U, b, V, P, S, hmid, hfb, hx₁, hx₂, hP⟩

private theorem croch_long_final_prefix {T : Type*}
    (f : TernaryAlphabet → List T)
    (htest : ∀ w : List TernaryAlphabet, w.length ≤ 5 →
      IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f))
    {a b c : TernaryAlphabet} {U V : List TernaryAlphabet}
    {pa A P S C sc x : List T}
    (hq : IsSquareFreeWord (a :: U ++ b :: V ++ [c]))
    (hlen : 3 ≤ U.length + V.length) (hfa : f a = pa ++ A)
    (hfc : f c = C ++ sc)
    (hx₁ : x = A ++ U.flatMap f ++ P) (hx₂ : x = S ++ V.flatMap f ++ C)
    (hlong : (U.flatMap f ++ P).length < C.length) : False := by
  have hLP : (U.flatMap f ++ P).IsSuffix x :=
    ⟨A, by simpa [List.append_assoc] using hx₁.symm⟩
  have hC : C.IsSuffix x := ⟨S ++ V.flatMap f, by simpa [List.append_assoc] using hx₂.symm⟩
  obtain ⟨d, hCd⟩ := croch_suffix_factor hLP hC (Nat.le_of_lt hlong)
  have hd : d ≠ [] := by
    intro hd
    subst d
    simp only [List.nil_append] at hCd
    have := congrArg List.length hCd
    omega
  have hAeq : A = S ++ V.flatMap f ++ d := by
    apply (List.append_left_inj (U.flatMap f ++ P)).mp
    calc
      A ++ (U.flatMap f ++ P) = x := by simpa [List.append_assoc] using hx₁.symm
      _ = (S ++ V.flatMap f) ++ C := hx₂
      _ = (S ++ V.flatMap f ++ d) ++ (U.flatMap f ++ P) := by
        rw [hCd]
        simp [List.append_assoc]
  have hds : d.IsSuffix (f a) := by
    apply List.IsSuffix.trans (l₂ := A)
    · exact ⟨S ++ V.flatMap f, hAeq.symm⟩
    · exact ⟨pa, hfa.symm⟩
  have hdp : d.IsPrefix (f c) := by
    apply List.IsPrefix.trans (l₂ := C)
    · exact ⟨U.flatMap f ++ P, hCd.symm⟩
    · exact ⟨sc, hfc.symm⟩
  have hac : a = c := by
    by_contra hac
    exact croch_no_image_overlap f htest hac hd hds hdp
  subst c
  by_cases hU : U = []
  · subst U
    have hV : V ≠ [] := by intro h; subst V; simp at hlen
    let z := V.getLast hV
    have hflat : V.flatMap f = V.dropLast.flatMap f ++ f z := by
      rw [← List.dropLast_append_getLast hV]
      simp [z]
    have hza : z ≠ a := by
      apply croch_ne_of_pair_infix hq
      refine ⟨a :: b :: V.dropLast, [], ?_⟩
      rw [← List.dropLast_append_getLast hV]
      simp [z, List.append_assoc]
    have hzds : (f z ++ d).IsSuffix (f a) := by
      apply List.IsSuffix.trans (l₂ := A)
      · refine ⟨S ++ V.dropLast.flatMap f, ?_⟩
        rw [hAeq, hflat]
        simp [List.append_assoc]
      · exact ⟨pa, hfa.symm⟩
    exact croch_no_suffix_overlap f htest hza hd hdp hzds
  · cases U with
    | nil => exact (hU rfl).elim
    | cons z U =>
      have haz : a ≠ z := croch_ne_of_pair_infix hq ⟨[], U ++ b :: V ++ [a], by simp⟩
      have hdp' : (d ++ f z).IsPrefix (f a) := by
        apply List.IsPrefix.trans (l₂ := C)
        · refine ⟨U.flatMap f ++ P, ?_⟩
          rw [hCd]
          simp [List.append_assoc]
        · exact ⟨sc, hfc.symm⟩
      exact croch_no_prefix_overlap f htest haz hd hds hdp'

private theorem croch_minimal_square {T : Type*} {W x y : List T}
    (hmin : ∀ {z : List T}, z ≠ [] → (z ++ z).IsInfix W → x.length ≤ z.length)
    (hy : y ≠ []) (hyy : (y ++ y).IsInfix W) (hyx : y.length < x.length) : False := by
  have := hmin hy hyy
  omega

private theorem croch_short_final_prefix {T : Type*}
    (f : TernaryAlphabet → List T) (hne : ∀ a, f a ≠ [])
    (htest : ∀ w : List TernaryAlphabet, w.length ≤ 5 →
      IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f))
    {W : List T} {a b c : TernaryAlphabet} {U V : List TernaryAlphabet}
    {pa A P S C sc x : List T}
    (hq : IsSquareFreeWord (a :: U ++ b :: V ++ [c]))
    (hqW : ((a :: U ++ b :: V ++ [c]).flatMap f).IsInfix W)
    (hmin : ∀ {z : List T}, z ≠ [] → (z ++ z).IsInfix W → x.length ≤ z.length)
    (hlen : 3 ≤ U.length + V.length) (hCne : C ≠ [])
    (hfa : f a = pa ++ A) (hfb : f b = P ++ S) (hfc : f c = C ++ sc)
    (hx₁ : x = A ++ U.flatMap f ++ P) (hx₂ : x = S ++ V.flatMap f ++ C)
    (hshort : C.length < P.length) : False := by
  have hP : P.IsSuffix x :=
    ⟨A ++ U.flatMap f, by simpa [List.append_assoc] using hx₁.symm⟩
  have hC : C.IsSuffix x :=
    ⟨S ++ V.flatMap f, by simpa [List.append_assoc] using hx₂.symm⟩
  obtain ⟨d, hPd⟩ := croch_suffix_factor hC hP (Nat.le_of_lt hshort)
  have hd : d ≠ [] := by
    intro hd
    subst d
    simp only [List.nil_append] at hPd
    have := congrArg List.length hPd
    omega
  have hcancel : A ++ U.flatMap f ++ d = S ++ V.flatMap f := by
    apply (List.append_left_inj C).mp
    calc
      (A ++ U.flatMap f ++ d) ++ C = A ++ U.flatMap f ++ P := by
        rw [hPd]
        simp [List.append_assoc]
      _ = x := hx₁.symm
      _ = (S ++ V.flatMap f) ++ C := hx₂
  have hbound := (croch_endpoint_bounds f htest hq hlen hfa hfb hfc hx₁ hx₂).1
  have hxlen := congrArg List.length hx₁
  simp only [List.length_append] at hxlen hbound
  have hSlen : S.length ≤ (A ++ U.flatMap f).length := by
    simp only [List.length_append]
    omega
  have hSpre : S.IsPrefix x :=
    ⟨V.flatMap f ++ C, by simpa [List.append_assoc] using hx₂.symm⟩
  have hALpre : (A ++ U.flatMap f).IsPrefix x :=
    ⟨P, by simpa [List.append_assoc] using hx₁.symm⟩
  obtain ⟨v, hAL⟩ := croch_prefix_factor hSpre hALpre hSlen
  have hVeq : V.flatMap f = v ++ d := by
    apply (List.append_right_inj S).mp
    calc
      S ++ V.flatMap f = A ++ U.flatMap f ++ d := hcancel.symm
      _ = (S ++ v) ++ d := by rw [hAL]
      _ = S ++ (v ++ d) := by simp [List.append_assoc]
  have hdsuf : d.IsSuffix (V.flatMap f) := ⟨v, hVeq.symm⟩
  obtain ⟨V₀, z, D, t, s, hV, hfz, hds, hsne⟩ := croch_suffix_cover f hne hd hdsuf
  by_cases hD : D = []
  · subst D
    simp only [List.flatMap_nil, List.append_nil] at hds
    subst s
    have hdp : d.IsPrefix (f b) := by
      apply List.IsPrefix.trans (l₂ := P)
      · exact ⟨C, hPd.symm⟩
      · exact ⟨S, hfb.symm⟩
    have hzs : d.IsSuffix (f z) := ⟨t, hfz.symm⟩
    have hzb : z = b := by
      by_contra hzb
      exact croch_no_image_overlap f htest hzb hd hzs hdp
    subst z
    have hfb' : f b = d ++ C ++ S := by rw [hfb, hPd]
    have htne : t ≠ [] := by
      intro ht
      subst t
      simp only [List.nil_append] at hfz
      have hlenfb := congrArg List.length (hfz.symm.trans hfb')
      simp only [List.length_append] at hlenfb
      have : C = [] := List.length_eq_zero_iff.mp (by omega)
      exact hCne this
    have himage : (a :: U ++ b :: V ++ [c]).flatMap f = pa ++ (x ++ x) ++ sc := by
      calc
        (a :: U ++ b :: V ++ [c]).flatMap f =
            pa ++ ((A ++ U.flatMap f ++ P) ++ (S ++ V.flatMap f ++ C)) ++ sc := by
              simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
                List.append_nil]
              rw [hfa, hfb, hfc]
              simp [List.append_assoc]
        _ = pa ++ (x ++ x) ++ sc := by rw [← hx₁, ← hx₂]
    have hxdecomp : x = S ++ V₀.flatMap f ++ t ++ d ++ C := by
      rw [hx₂, hV]
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [hfz]
      simp [List.append_assoc]
    have hsq : (t ++ t).IsInfix ((a :: U ++ b :: V ++ [c]).flatMap f) := by
      refine ⟨pa ++ S ++ V₀.flatMap f, d ++ V.flatMap f ++ C ++ sc, ?_⟩
      have hrel : t ++ d = d ++ C ++ S := hfz.symm.trans hfb'
      have hboundary : t ++ d ++ C ++ S = t ++ t ++ d := by
        calc
          t ++ d ++ C ++ S = t ++ (d ++ C ++ S) := by simp [List.append_assoc]
          _ = t ++ (t ++ d) := by rw [← hrel]
          _ = t ++ t ++ d := by simp [List.append_assoc]
      have hboundary' := congrArg
        (fun z => z ++ (V.flatMap f ++ C ++ sc)) hboundary.symm
      calc
        (pa ++ S ++ V₀.flatMap f) ++ (t ++ t) ++
            (d ++ V.flatMap f ++ C ++ sc) = pa ++ S ++ V₀.flatMap f ++
              ((t ++ t ++ d) ++ (V.flatMap f ++ C ++ sc)) := by
                simp [List.append_assoc]
        _ = pa ++ S ++ V₀.flatMap f ++
              ((t ++ d ++ C ++ S) ++ (V.flatMap f ++ C ++ sc)) := by rw [hboundary']
        _ = pa ++ ((S ++ V₀.flatMap f ++ t ++ d ++ C) ++
              (S ++ V.flatMap f ++ C)) ++ sc := by simp [List.append_assoc]
        _ = pa ++ (x ++ x) ++ sc := by rw [← hxdecomp, ← hx₂]
        _ = (a :: U ++ b :: V ++ [c]).flatMap f := himage.symm
    have htblen : (f b).length ≤ x.length := by
      have : (f b).IsInfix x := by
        refine ⟨S ++ V₀.flatMap f, C, ?_⟩
        rw [hx₂, hV]
        simp [List.append_assoc]
      exact this.length_le
    have htlen := congrArg List.length hfz
    simp only [List.length_append] at htlen
    have hdpos : 0 < d.length := List.length_pos_iff.mpr hd
    exact croch_minimal_square hmin htne (hsq.trans hqW) (by omega)
  · cases D with
    | nil => exact (hD rfl).elim
    | cons y D =>
      have hzy : z ≠ y := by
        apply croch_ne_of_pair_infix hq
        refine ⟨a :: U ++ b :: V₀, D ++ [c], ?_⟩
        rw [hV]
        simp [List.append_assoc]
      have hsp : (s ++ f y).IsPrefix (f b) := by
        apply List.IsPrefix.trans (l₂ := d)
        · refine ⟨D.flatMap f, ?_⟩
          rw [hds]
          simp [List.append_assoc]
        · apply List.IsPrefix.trans (l₂ := P)
          · exact ⟨C, hPd.symm⟩
          · exact ⟨S, hfb.symm⟩
      exact croch_no_prefix_overlap f htest hzy hsne ⟨t, hfz.symm⟩ hsp

private theorem croch_middle_final_prefix {T : Type*}
    (f : TernaryAlphabet → List T) (hne : ∀ a, f a ≠ [])
    (htest : ∀ w : List TernaryAlphabet, w.length ≤ 5 →
      IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f))
    {W : List T} {a b c : TernaryAlphabet} {U V : List TernaryAlphabet}
    {pa A P S C sc x : List T}
    (hq : IsSquareFreeWord (a :: U ++ b :: V ++ [c]))
    (hqW : ((a :: U ++ b :: V ++ [c]).flatMap f).IsInfix W)
    (hmin : ∀ {z : List T}, z ≠ [] → (z ++ z).IsInfix W → x.length ≤ z.length)
    (hAne : A ≠ []) (hPne : P ≠ [])
    (hfa : f a = pa ++ A) (hfb : f b = P ++ S) (hfc : f c = C ++ sc)
    (hx₁ : x = A ++ U.flatMap f ++ P) (hx₂ : x = S ++ V.flatMap f ++ C)
    (hmiddle : P.length ≤ C.length ∧ C.length ≤ (U.flatMap f ++ P).length) : False := by
  have hP : P.IsSuffix x :=
    ⟨A ++ U.flatMap f, by simpa [List.append_assoc] using hx₁.symm⟩
  have hC : C.IsSuffix x :=
    ⟨S ++ V.flatMap f, by simpa [List.append_assoc] using hx₂.symm⟩
  obtain ⟨d, hCd⟩ := croch_suffix_factor hP hC hmiddle.1
  have hUP : (U.flatMap f ++ P).IsSuffix x :=
    ⟨A, by simpa [List.append_assoc] using hx₁.symm⟩
  obtain ⟨e, hUPe⟩ := croch_suffix_factor hC hUP hmiddle.2
  have hUde : U.flatMap f = e ++ d := by
    apply (List.append_left_inj P).mp
    calc
      U.flatMap f ++ P = e ++ C := hUPe
      _ = (e ++ d) ++ P := by rw [hCd]; simp [List.append_assoc]
  by_cases hd : d = []
  · subst d
    simp only [List.nil_append] at hCd
    subst C
    have hcancel : A ++ U.flatMap f = S ++ V.flatMap f := by
      apply (List.append_left_inj P).mp
      calc
        (A ++ U.flatMap f) ++ P = x := by simpa [List.append_assoc] using hx₁.symm
        _ = (S ++ V.flatMap f) ++ P := by simpa [List.append_assoc] using hx₂
    rcases croch_suffix_parse f hne (croch_eq_of_image_suffix f hne htest)
        ⟨pa, hfa.symm⟩ ⟨P, hfb.symm⟩ hcancel with hsame | hextra | hextra
    · rcases hsame with ⟨rfl, rfl⟩
      have hab : a ≠ b := by
        intro hab
        subst b
        apply hq ((a :: U) ++ (a :: U))
        · exact ⟨[], [c], by simp [List.append_assoc]⟩
        · exact ⟨a :: U, by simp, rfl⟩
      have hbc : b ≠ c := by
        intro hbc
        subst c
        apply hq ((U ++ [b]) ++ (U ++ [b]))
        · exact ⟨[a], [], by simp [List.append_assoc]⟩
        · exact ⟨U ++ [b], by simp, rfl⟩
      have hout := htest [a, b, c] (by simp) (croch_squarefree_triple hab hbc)
      apply hout ((A ++ P) ++ (A ++ P))
      · refine ⟨pa, sc, ?_⟩
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [hfa, hfb, hfc]
        simp [List.append_assoc]
      · exact ⟨A ++ P, by simp [hPne], rfl⟩
    · rcases hextra with ⟨rfl, rfl, rfl⟩
      have hbc : b ≠ c := by
        intro hbc
        subst c
        apply hq ((a :: U ++ [b]) ++ (a :: U ++ [b]))
        · exact ⟨[], [], by simp [List.append_assoc]⟩
        · exact ⟨a :: U ++ [b], by simp, rfl⟩
      have hout := htest [b, c] (by simp) (croch_squarefree_pair hbc)
      apply hout (P ++ P)
      · refine ⟨[], sc, ?_⟩
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
        rw [hfb, hfc]
        simp
      · exact ⟨P, hPne, rfl⟩
    · exact hAne hextra.2.1
  · have hdsuf : d.IsSuffix (U.flatMap f) := ⟨e, hUde.symm⟩
    obtain ⟨U₀, z, D, t, s, hU, hfz, hds, hsne⟩ :=
      croch_suffix_cover f hne hd hdsuf
    cases D with
    | cons y D =>
      have hzy : z ≠ y := by
        apply croch_ne_of_pair_infix hq
        refine ⟨a :: U₀, D ++ b :: V ++ [c], ?_⟩
        rw [hU]
        simp [List.append_assoc]
      have hsp : (s ++ f y).IsPrefix (f c) := by
        apply List.IsPrefix.trans (l₂ := d)
        · refine ⟨D.flatMap f, ?_⟩
          rw [hds]
          simp [List.append_assoc]
        · apply List.IsPrefix.trans (l₂ := C)
          · exact ⟨P, hCd.symm⟩
          · exact ⟨sc, hfc.symm⟩
      exact croch_no_prefix_overlap f htest hzy hsne ⟨t, hfz.symm⟩ hsp
    | nil =>
      simp only [List.flatMap_nil, List.append_nil] at hds
      subst s
      have hdp : d.IsPrefix (f c) := by
        apply List.IsPrefix.trans (l₂ := C)
        · exact ⟨P, hCd.symm⟩
        · exact ⟨sc, hfc.symm⟩
      have hzs : d.IsSuffix (f z) := ⟨t, hfz.symm⟩
      have hzc : z = c := by
        by_contra hzc
        exact croch_no_image_overlap f htest hzc hd hzs hdp
      subst z
      have hrel : t ++ d = d ++ P ++ sc := by
        calc
          t ++ d = f c := hfz.symm
          _ = C ++ sc := hfc
          _ = d ++ P ++ sc := by rw [hCd]
      have htne : t ≠ [] := by
        intro ht
        subst t
        simp only [List.nil_append] at hrel
        have hlen := congrArg List.length hrel
        simp only [List.length_append] at hlen
        have hPzero : P.length = 0 := by omega
        exact hPne (List.length_eq_zero_iff.mp hPzero)
      have himage : (a :: U ++ b :: V ++ [c]).flatMap f = pa ++ (x ++ x) ++ sc := by
        calc
          (a :: U ++ b :: V ++ [c]).flatMap f =
              pa ++ ((A ++ U.flatMap f ++ P) ++ (S ++ V.flatMap f ++ C)) ++ sc := by
                simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
                  List.append_nil]
                rw [hfa, hfb, hfc]
                simp [List.append_assoc]
          _ = pa ++ (x ++ x) ++ sc := by rw [← hx₁, ← hx₂]
      have hxdecomp : x = A ++ U₀.flatMap f ++ t ++ d ++ P := by
        rw [hx₁, hU]
        simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [hfz]
        simp [List.append_assoc]
      have hboundary : t ++ t ++ d = t ++ d ++ P ++ sc := by
        calc
          t ++ t ++ d = t ++ (t ++ d) := by simp [List.append_assoc]
          _ = t ++ (d ++ P ++ sc) := by rw [hrel]
          _ = t ++ d ++ P ++ sc := by simp [List.append_assoc]
      have hsq : (t ++ t).IsInfix ((a :: U ++ b :: V ++ [c]).flatMap f) := by
        refine ⟨pa ++ x ++ A ++ U₀.flatMap f, d, ?_⟩
        calc
          (pa ++ x ++ A ++ U₀.flatMap f) ++ (t ++ t) ++ d =
              pa ++ x ++ (A ++ U₀.flatMap f ++ (t ++ t ++ d)) := by
                simp [List.append_assoc]
          _ = pa ++ x ++ (A ++ U₀.flatMap f ++ (t ++ d ++ P ++ sc)) := by
                rw [hboundary]
          _ = pa ++ (x ++ x) ++ sc := by rw [hxdecomp]; simp [List.append_assoc]
          _ = (a :: U ++ b :: V ++ [c]).flatMap f := himage.symm
      have hfcin : (f c).IsInfix x := by
        refine ⟨A ++ U₀.flatMap f, P, ?_⟩
        rw [hx₁, hU]
        simp [hfz, List.append_assoc]
      have htlen := congrArg List.length hfz
      simp only [List.length_append] at htlen
      have hdpos : 0 < d.length := List.length_pos_iff.mpr hd
      exact croch_minimal_square hmin htne (hsq.trans hqW)
        (by have := hfcin.length_le; omega)

private theorem croch_synchronize_minimal_square {T : Type*}
    (f : TernaryAlphabet → List T) (hne : ∀ a, f a ≠ [])
    (htest : ∀ w : List TernaryAlphabet, w.length ≤ 5 →
      IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f))
    {W : List T} {a c : TernaryAlphabet} {mid : List TernaryAlphabet}
    {pa A C sc x : List T} (hx : x ≠ [])
    (hq : IsSquareFreeWord (a :: mid ++ [c]))
    (hqW : ((a :: mid ++ [c]).flatMap f).IsInfix W)
    (hmin : ∀ {z : List T}, z ≠ [] → (z ++ z).IsInfix W → x.length ≤ z.length)
    (hfa : f a = pa ++ A) (hfc : f c = C ++ sc)
    (hxx : x ++ x = A ++ mid.flatMap f ++ C) (hAne : A ≠ []) (hCne : C ≠ []) : False := by
  have hmidlen := croch_middle_length f htest hx hq hfa hfc hxx
  obtain ⟨U, b, V, P, S, hmid, hfb, hx₁, hx₂, hPne⟩ :=
    croch_midpoint_cover_prefix f hne htest hx hCne hq hmidlen hfa hfc hxx
  subst mid
  have hlen : 3 ≤ U.length + V.length := by
    simp only [List.length_append, List.length_cons] at hmidlen
    omega
  by_cases hshort : C.length < P.length
  · exact croch_short_final_prefix f hne htest hq hqW hmin hlen hCne
      hfa hfb hfc hx₁ hx₂ hshort
  by_cases hlong : (U.flatMap f ++ P).length < C.length
  · exact croch_long_final_prefix f htest hq hlen hfa hfc hx₁ hx₂ hlong
  · exact croch_middle_final_prefix f hne htest hq hqW hmin hAne hPne
      hfa hfb hfc hx₁ hx₂ ⟨Nat.le_of_not_gt hshort, Nat.le_of_not_gt hlong⟩

/-- **Crochemore's square-freeness test.** Let $f$ map each letter of the three-letter alphabet
$\{a, b, c\}$ to a finite word over a set $T$, and extend $f$ to words by concatenation,
$f(x_1 \cdots x_n) = f(x_1) \cdots f(x_n)$. Then $f$ maps every square-free word over
$\{a, b, c\}$ to a square-free word if and only if it maps every square-free word over
$\{a, b, c\}$ of length at most $5$ to a square-free word.

A word is square-free when no factor has the form $uu$ with $u$ nonempty. No non-erasing
hypothesis is assumed: the image of a letter may be empty.

Proof: reduce erasing morphisms first, then apply Currie's synchronization
method to a shortest square occurrence and its shortest source-word cover.

Proves `Wanted` entry `crochemore_squarefree_test_set`.

Source: Currie, lines 99-100 of
`https://cs.uwaterloo.ca/journals/JIS/VOL22/Currie/currie20.tex`, span SHA-256
`ae0ba8107ccc5dfcd1a4065609be8a31f1a809ea3f1f9b37ce7a2cd762dd5bf9`; primary reference
Crochemore, Theoret. Comput. Sci. 18(2) (1982), DOI 10.1016/0304-3975(82)90023-8.
-/
public theorem crochemore_squarefree_test_set
    {T : Type*} (f : TernaryAlphabet → List T) :
    (∀ w : List TernaryAlphabet, IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f)) ↔
      ∀ w : List TernaryAlphabet, w.length ≤ 5 →
        IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f) := by
  classical
  constructor
  · intro hall w _ hw
    exact hall w hw
  · intro htest w hw
    rcases croch_empty_or_nonempty f htest with hall | hne
    · have himage : w.flatMap f = [] :=
        List.flatMap_eq_nil_iff.mpr fun a _ => hall a
      rw [himage]
      exact croch_squarefree_of_length_le_three [] (by simp) (by simp)
    · by_contra hbad
      rw [IsSquareFreeWord] at hbad
      push Not at hbad
      obtain ⟨s, hs, y, hy, hsy⟩ := hbad
      subst s
      let p : Nat → Prop := fun n => ∃ z : List T,
        z ≠ [] ∧ z.length = n ∧ (z ++ z).IsInfix (w.flatMap f)
      have hp : ∃ n, p n := ⟨y.length, y, hy, rfl, hs⟩
      obtain ⟨x, hx, hxlen, hxx⟩ := Nat.find_spec hp
      have hmin : ∀ {z : List T}, z ≠ [] → (z ++ z).IsInfix (w.flatMap f) →
          x.length ≤ z.length := by
        intro z hz hzz
        rw [hxlen]
        exact Nat.find_min' hp ⟨z, hz, rfl, hzz⟩
      obtain ⟨pre, a, mid, c, post, pa, A, C, sc, hwcover, hfa, hfc,
          hxxeq, hAne, hCne⟩ := croch_square_cover f hne htest hx hxx
      have hqinf : (a :: mid ++ [c]).IsInfix w := by
        refine ⟨pre, post, ?_⟩
        rw [hwcover]
        simp [List.append_assoc]
      exact croch_synchronize_minimal_square f hne htest hx
        (hw.of_isInfix hqinf) (hqinf.flatMap f) hmin hfa hfc hxxeq hAne hCne

end MetaMathlibExt
