/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# String rewriting and its reduction to the modified Post correspondence problem
-/
module

public import CSLibExt.Computability.Decidability.PCP

/-!
# String rewriting and its reduction to the modified Post correspondence problem

A **string rewriting system** (semi-Thue system) is a finite list `R` of rules `(l, r)`; a step
replaces one occurrence of `l` in a word by `r` (`Step`), and `Derives R x y` is the
reflexive-transitive closure. The **reachability problem** `SR (R, x, y)` asks whether `x` rewrites
to `y`. It is directed: the semi-Thue word problem instead asks whether `x` and `y` are equivalent
under the symmetric closure of the rules.

`toMPCP (R, x, y)` is the classical reduction to the modified Post correspondence problem, over
the alphabet `α` extended with a row separator `#` (`Post.star`) and an end marker `$`
(`Post.endMark`):

* the first domino `($, $x#)` puts the start word on the bottom;
* each rule `(l, r)` gives the domino `(l, r)`, and each letter `a` the copy domino `(a, a)`;
* the separator domino `(#, #)` closes a row, and the final domino `(y#$, $)` lets the top
  catch up once the bottom has reached `y`.

A solution spells a derivation `x = x₀ ⇒* x₁ ⇒* ... ⇒* xₙ = y` row by row: the top reads
`$x₀#x₁#...xₙ#$` one row behind the bottom (`sr_iff_mpcp_toMPCP`). Each row rewrites several
disjoint occurrences at once, which `Derives` absorbs. The backward direction is an induction
over the dominoes that tracks the unread rest of the current row (`derives_of_top_eq`).

The dominoes have nonempty words when the rules do, so with `Post.manyOneReducible_mpcp_pcp`
reachability for rules with nonempty sides many-one reduces to PCP
(`manyOneReducible_sr_pcp`).

## Main results

- `Step`, `Derives`, `SR` : rewriting steps, derivations and the reachability problem.
- `sr_iff_mpcp_toMPCP` : `SR I ↔ MPCP (toMPCP I)`.
- `manyOneReducible_sr_mpcp`, `manyOneReducible_sr_pcp` : on rules with nonempty sides, the
  reachability problem many-one reduces to MPCP (with nonempty words) and to PCP.
- `ThueWP` : the word problem of the Thue system of the rules (equivalence under the
  symmetric closure).

## References

* E. L. Post, *A variant of a recursively unsolvable problem*, Bull. AMS 52 (1946), 264–268.
* Y. Forster, E. Heiter, G. Smolka, *Verification of PCP-related computational reductions in
  Coq*, ITP 2018, LNCS 10895, 253–269.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability.Rewriting

open Post

variable {α : Type*}

/-- A rewriting rule `(l, r)`: replace an occurrence of `l` by `r`. -/
abbrev Rule (α : Type*) := List α × List α

/-- One rewriting step of the system `R`: replace one occurrence of a left side by its right
side. -/
inductive Step (R : List (Rule α)) : List α → List α → Prop
  | mk {l r : List α} (u v : List α) : (l, r) ∈ R → Step R (u ++ l ++ v) (u ++ r ++ v)

/-- `Derives R x y`: `x` rewrites to `y` in zero or more steps. -/
def Derives (R : List (Rule α)) : List α → List α → Prop := Relation.ReflTransGen (Step R)

/-- The **reachability problem** for string rewriting: on the instance `(R, x, y)`, does `x`
rewrite to `y`? -/
def SR (I : List (Rule α) × List α × List α) : Prop := Derives I.1 I.2.1 I.2.2

/-- Every rule has a nonempty left side and a nonempty right side. -/
def NonemptyRules (R : List (Rule α)) : Prop := ∀ r ∈ R, r.1 ≠ [] ∧ r.2 ≠ []

/-! ### Derivations -/

section Derives

variable {R : List (Rule α)}

theorem Step.append_left {x y : List α} (h : Step R x y) (p : List α) :
    Step R (p ++ x) (p ++ y) := by
  obtain ⟨u, v, hr⟩ := h
  simpa only [List.append_assoc] using Step.mk (p ++ u) v hr

theorem Step.append_right {x y : List α} (h : Step R x y) (q : List α) :
    Step R (x ++ q) (y ++ q) := by
  obtain ⟨u, v, hr⟩ := h
  simpa only [List.append_assoc] using Step.mk u (v ++ q) hr

theorem Step.of_mem {l r : List α} (h : (l, r) ∈ R) : Step R l r := by
  simpa using Step.mk [] [] h

theorem Derives.refl (x : List α) : Derives R x x := Relation.ReflTransGen.refl

theorem Derives.single {x y : List α} (h : Step R x y) : Derives R x y :=
  Relation.ReflTransGen.single h

theorem Derives.trans {x y z : List α} (h₁ : Derives R x y) (h₂ : Derives R y z) :
    Derives R x z :=
  Relation.ReflTransGen.trans h₁ h₂

theorem Derives.append_left {x y : List α} (h : Derives R x y) (p : List α) :
    Derives R (p ++ x) (p ++ y) :=
  Relation.ReflTransGen.lift (p ++ ·) (fun _ _ (h' : Step R _ _) ↦ h'.append_left p) _ _ h

theorem Derives.append_right {x y : List α} (h : Derives R x y) (q : List α) :
    Derives R (x ++ q) (y ++ q) :=
  Relation.ReflTransGen.lift (· ++ q) (fun _ _ (h' : Step R _ _) ↦ h'.append_right q) _ _ h

theorem Derives.append {a b c d : List α} (h₁ : Derives R a b) (h₂ : Derives R c d) :
    Derives R (a ++ c) (b ++ d) :=
  (h₁.append_right c).trans (h₂.append_left b)

end Derives

/-! ### The dominoes -/

/-- A word over `α` as a word of letters of `Sym α`. -/
abbrev lift (u : List α) : List (Sym α) := u.map letter

/-- The first domino `($, $x#)`. -/
def startCard (x : List α) : Domino (Sym α) := ([endMark], endMark :: lift x ++ [star])

/-- The final domino `(y#$, $)`. -/
def finalCard (y : List α) : Domino (Sym α) := (lift y ++ [star, endMark], [endMark])

/-- The row separator `(#, #)`. -/
def sepCard : Domino (Sym α) := ([star], [star])

/-- The domino `(l, r)` of a rule. -/
def ruleCard (r : Rule α) : Domino (Sym α) := (lift r.1, lift r.2)

/-- The copy domino `(a, a)` of a letter. -/
def copyCard (a : α) : Domino (Sym α) := ([letter a], [letter a])

/-- The letters of an instance: those of the rules and of both words. -/
def symbols (I : List (Rule α) × List α × List α) : List α :=
  I.1.flatMap (fun r ↦ r.1 ++ r.2) ++ I.2.1 ++ I.2.2

/-- The MPCP instance of a reachability problem. Its first domino is `startCard x`. -/
def toMPCP (I : List (Rule α) × List α × List α) : List (Domino (Sym α)) :=
  startCard I.2.1 :: finalCard I.2.2 :: sepCard :: (I.1.map ruleCard ++ (symbols I).map copyCard)

theorem mem_toMPCP {I : List (Rule α) × List α × List α} {c : Domino (Sym α)} :
    c ∈ toMPCP I ↔ c = startCard I.2.1 ∨ c = finalCard I.2.2 ∨ c = sepCard ∨
      (∃ r ∈ I.1, c = ruleCard r) ∨ ∃ a ∈ symbols I, c = copyCard a := by
  simp only [toMPCP, List.mem_cons, List.mem_append, List.mem_map]
  constructor
  · rintro (h | h | h | ⟨r, hr, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, rfl⟩)))
  · rintro (h | h | h | ⟨r, hr, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, rfl⟩)))

theorem top_map_copyCard (u : List α) : top (u.map copyCard) = lift u := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.map_cons, top_cons, ih]; rfl

theorem bottom_map_copyCard (u : List α) : bottom (u.map copyCard) = lift u := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.map_cons, bottom_cons, ih]; rfl

/-! ### Comparing words of letters with separators -/

theorem letter_ne_star (a : α) : letter a ≠ star := by simp

theorem letter_ne_endMark (a : α) : letter a ≠ endMark := by simp

/-- If `uX` equals `v#Y` and `u`, `v` are words of letters, then `u` is a prefix of `v`. -/
theorem exists_of_lift_append_eq {u v : List α} {X Y : List (Sym α)}
    (h : lift u ++ X = lift v ++ star :: Y) : ∃ w, v = u ++ w ∧ X = lift w ++ star :: Y := by
  induction u generalizing v with
  | nil => exact ⟨v, rfl, h⟩
  | cons a u ih =>
    cases v with
    | nil => exact absurd (List.cons.inj h).1 (letter_ne_star a)
    | cons b v =>
      obtain ⟨hab, h⟩ := List.cons.inj h
      obtain ⟨w, rfl, hX⟩ := ih h
      exact ⟨w, by rw [Option.some.inj (Option.some.inj hab)]; rfl, hX⟩

theorem eq_of_lift_append_star_eq {u v : List α} {X Y : List (Sym α)}
    (h : lift u ++ star :: X = lift v ++ star :: Y) : u = v ∧ X = Y := by
  obtain ⟨w, rfl, hX⟩ := exists_of_lift_append_eq h
  cases w with
  | nil => exact ⟨(List.append_nil u).symm, (List.cons.inj hX).2⟩
  | cons b w => exact absurd (List.cons.inj hX).1 (letter_ne_star b).symm

theorem eq_nil_of_star_cons_eq {v : List α} {X Y : List (Sym α)}
    (h : star :: X = lift v ++ star :: Y) : v = [] ∧ X = Y := by
  cases v with
  | nil => exact ⟨rfl, (List.cons.inj h).2⟩
  | cons b v => exact absurd (List.cons.inj h).1 (letter_ne_star b).symm

theorem not_endMark_cons_eq {v : List α} {X Y : List (Sym α)} :
    ¬endMark :: X = lift v ++ star :: Y := by
  intro h
  cases v with
  | nil => exact absurd (List.cons.inj h).1 (by simp)
  | cons b v => exact absurd (List.cons.inj h).1 (letter_ne_endMark b).symm

theorem eq_nil_of_endMark_cons_eq {t : List α} {X Y : List (Sym α)}
    (h : endMark :: X = lift t ++ endMark :: Y) : t = [] := by
  cases t with
  | nil => rfl
  | cons b t => exact absurd (List.cons.inj h).1 (letter_ne_endMark b).symm

/-! ### From solutions to derivations -/

variable {I : List (Rule α) × List α × List α}

/-- **The backward direction.** Reading dominoes left to right, `s` is the part of the current
row already matched, with bottoms `t` (so `s ⇒* t`), and `v` is the rest of the row still to be
matched on top. Then `s v ⇒* y`. -/
theorem derives_of_top_eq : ∀ (A : List (Domino (Sym α))), (∀ c ∈ A, c ∈ toMPCP I) →
    ∀ (v s t : List α), Derives I.1 s t → top A = lift v ++ star :: (lift t ++ bottom A) →
      Derives I.1 (s ++ v) I.2.2
  | [], _, v, s, t, _, h => by simp [top] at h
  | c :: A, hA, v, s, t, hst, h => by
    rw [top_cons, bottom_cons] at h
    have ih := derives_of_top_eq A fun d hd ↦ hA d (List.mem_cons_of_mem c hd)
    rcases mem_toMPCP.mp (hA c List.mem_cons_self) with
      rfl | rfl | rfl | ⟨⟨l, r⟩, hr, rfl⟩ | ⟨a, -, rfl⟩
    · exact absurd h not_endMark_cons_eq
    · -- the final domino: the row read so far is `y`, and its bottom is empty
      simp only [finalCard, List.append_assoc, List.cons_append, List.nil_append] at h
      obtain ⟨rfl, h'⟩ := eq_of_lift_append_star_eq h
      obtain rfl := eq_nil_of_endMark_cons_eq h'
      simpa using hst.append_right I.2.2
    · -- the separator: the row is complete, and the next row starts from `t`
      simp only [sepCard, List.cons_append, List.nil_append] at h
      obtain ⟨rfl, h'⟩ := eq_nil_of_star_cons_eq h
      have := ih t [] [] (Derives.refl _) (by simpa using h')
      simpa using hst.trans (by simpa using this)
    · -- a rule domino `(l, r)`
      simp only [ruleCard] at h
      obtain ⟨w, rfl, h'⟩ := exists_of_lift_append_eq h
      have hst' : Derives I.1 (s ++ l) (t ++ r) := hst.append (Derives.single (Step.of_mem hr))
      have := ih w (s ++ l) (t ++ r) hst' (by simpa [List.append_assoc] using h')
      simpa [List.append_assoc] using this
    · -- a copy domino `(a, a)`
      simp only [copyCard, List.cons_append, List.nil_append] at h
      obtain ⟨w, rfl, h'⟩ := exists_of_lift_append_eq (u := [a]) (by simpa using h)
      have := ih w (s ++ [a]) (t ++ [a]) (hst.append_right [a])
        (by simpa [List.append_assoc] using h')
      simpa [List.append_assoc] using this

/-! ### From derivations to solutions -/

theorem mem_symbols_of_step {w w' : List α} (h : Step I.1 w w')
    (hw : ∀ a ∈ w, a ∈ symbols I) : ∀ a ∈ w', a ∈ symbols I := by
  obtain ⟨u, v, hr⟩ := h
  intro a ha
  simp only [List.mem_append] at ha hw
  rcases ha with (ha | ha) | ha
  · exact hw a (Or.inl (Or.inl ha))
  · simp only [symbols, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl ⟨_, hr, Or.inr ha⟩)
  · exact hw a (Or.inr ha)

/-- **The forward direction.** A derivation from `w` to `y` gives dominoes whose top is `w#`
followed by their bottom. -/
theorem exists_cards_of_derives {w : List α} (h : Derives I.1 w I.2.2) :
    (∀ a ∈ w, a ∈ symbols I) → ∃ A : List (Domino (Sym α)), (∀ c ∈ A, c ∈ toMPCP I) ∧
      top A = lift w ++ star :: bottom A := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _
    refine ⟨[finalCard I.2.2], fun c hc ↦ ?_, ?_⟩
    · rw [List.mem_singleton.mp hc]
      exact mem_toMPCP.mpr (Or.inr (Or.inl rfl))
    · simp [top, bottom, finalCard]
  | @head w w₁ hstep _ ih =>
    intro hw
    obtain ⟨A₁, hA₁, htop⟩ := ih (mem_symbols_of_step hstep hw)
    rcases hstep with @⟨l, r, u, v, hr⟩
    have hu : ∀ a ∈ u, a ∈ symbols I := fun a ha ↦ hw a (by simp [ha])
    have hv : ∀ a ∈ v, a ∈ symbols I := fun a ha ↦ hw a (by simp [ha])
    refine ⟨u.map copyCard ++ ruleCard (l, r) :: (v.map copyCard ++ sepCard :: A₁), ?_, ?_⟩
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.mem_map] at hc
      rcases hc with ⟨a, ha, rfl⟩ | rfl | ⟨a, ha, rfl⟩ | rfl | hc
      · exact mem_toMPCP.mpr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, hu a ha, rfl⟩))))
      · exact mem_toMPCP.mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hr, rfl⟩))))
      · exact mem_toMPCP.mpr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, hv a ha, rfl⟩))))
      · exact mem_toMPCP.mpr (Or.inr (Or.inr (Or.inl rfl)))
      · exact hA₁ c hc
    · simp only [top_append, bottom_append, top_cons, bottom_cons, top_map_copyCard,
        bottom_map_copyCard, htop, ruleCard, sepCard, lift, List.map_append]
      simp

/-- **Reachability reduces to MPCP**: `x ⇒* y` iff the dominoes of `toMPCP (R, x, y)` have a
solution starting with the first domino. -/
theorem sr_iff_mpcp_toMPCP : SR I ↔ MPCP (toMPCP I) := by
  constructor
  · intro h
    obtain ⟨A, hA, htop⟩ := exists_cards_of_derives h fun a ha ↦ by
      simp [symbols, ha]
    refine ⟨startCard I.2.1, A, rfl, List.cons_ne_nil _ _, fun c hc ↦ ?_, ?_⟩
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact mem_toMPCP.mpr (Or.inl rfl)
      · exact hA c hc
    · rw [top_cons, bottom_cons, htop]
      simp [startCard]
  · rintro ⟨d₀, s, hd₀, -, hmem, htop⟩
    obtain rfl : d₀ = startCard I.2.1 := (Option.some.inj hd₀).symm
    rw [top_cons, bottom_cons] at htop
    simp only [startCard, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at htop
    have := derives_of_top_eq s (fun c hc ↦ hmem c (List.mem_cons_of_mem _ hc)) I.2.1 [] []
      (Derives.refl _) (by simpa using htop)
    change Derives _ _ _
    simpa using this

theorem nonemptyWords_toMPCP (h : NonemptyRules I.1) : NonemptyWords (toMPCP I) := by
  intro c hc
  rcases mem_toMPCP.mp hc with rfl | rfl | rfl | ⟨r, hr, rfl⟩ | ⟨a, -, rfl⟩
  · simp [startCard]
  · simp [finalCard]
  · simp [sepCard]
  · simpa [ruleCard] using h r hr
  · simp [copyCard]

/-! ### The many-one reduction -/

/-- The total reduction: `toMPCP` when the rules have nonempty sides, and the unsolvable empty
instance otherwise. -/
def reduce (I : List (Rule α) × List α × List α) : List (Domino (Sym α)) :=
  cond (nonemptyWordsB I.1) (toMPCP I) []

theorem nonemptyRules_iff_nonemptyWords (R : List (Rule α)) :
    NonemptyRules R ↔ NonemptyWords R := Iff.rfl

theorem nonemptyRules_and_sr_iff (I : List (Rule α) × List α × List α) :
    NonemptyRules I.1 ∧ SR I ↔ NonemptyWords (reduce I) ∧ MPCP (reduce I) := by
  by_cases h : NonemptyRules I.1
  · have hb : nonemptyWordsB I.1 = true := nonemptyWordsB_iff.mpr h
    simp only [reduce, hb, Bool.cond_true]
    exact ⟨fun ⟨_, hs⟩ ↦ ⟨nonemptyWords_toMPCP h, sr_iff_mpcp_toMPCP.mp hs⟩,
      fun ⟨_, hm⟩ ↦ ⟨h, sr_iff_mpcp_toMPCP.mpr hm⟩⟩
  · have hb : nonemptyWordsB I.1 = false :=
      Bool.eq_false_iff.mpr fun hh ↦ h (nonemptyWordsB_iff.mp hh)
    simp only [reduce, hb, Bool.cond_false]
    exact ⟨fun ⟨h', _⟩ ↦ absurd h' h, fun ⟨_, d₀, _, hd₀, _⟩ ↦ by simp at hd₀⟩

section Computable

variable [Primcodable α]

theorem primrec_lift : Primrec (lift (α := α)) :=
  Primrec.list_map Primrec.id ((Primrec.option_some.comp Primrec.option_some).comp Primrec.snd).to₂

theorem primrec_toMPCP : Primrec (toMPCP (α := α)) := by
  have hstart : Primrec (startCard (α := α)) :=
    Primrec.pair (Primrec.const _) (Primrec.list_cons.comp (Primrec.const _)
      (Primrec.list_append.comp primrec_lift (Primrec.const _)))
  have hfinal : Primrec (finalCard (α := α)) :=
    Primrec.pair (Primrec.list_append.comp primrec_lift (Primrec.const _)) (Primrec.const _)
  have hrule : Primrec (ruleCard (α := α)) :=
    Primrec.pair (primrec_lift.comp Primrec.fst) (primrec_lift.comp Primrec.snd)
  have hcopy : Primrec (copyCard (α := α)) :=
    Primrec.pair (Primrec.list_cons.comp (Primrec.option_some.comp Primrec.option_some)
      (Primrec.const [])) (Primrec.list_cons.comp (Primrec.option_some.comp Primrec.option_some)
      (Primrec.const []))
  have hsym : Primrec (symbols (α := α)) :=
    Primrec.list_append.comp (Primrec.list_append.comp
      (Primrec.list_flatMap Primrec.fst (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_cons.comp (hstart.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.list_cons.comp (hfinal.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.const _)
        (Primrec.list_append.comp (Primrec.list_map Primrec.fst (hrule.comp Primrec.snd).to₂)
          (Primrec.list_map hsym (hcopy.comp Primrec.snd).to₂))))

theorem primrec_reduce : Primrec (reduce (α := α)) :=
  Primrec.cond (primrec_nonemptyWordsB.comp Primrec.fst) primrec_toMPCP (Primrec.const [])

/-- **Reachability many-one reduces to MPCP**, on rules with nonempty sides; the MPCP
instances have nonempty words. -/
theorem manyOneReducible_sr_mpcp :
    ManyOneReducible (fun I : List (Rule α) × List α × List α ↦ NonemptyRules I.1 ∧ SR I)
      (fun P : List (Domino (Sym α)) ↦ NonemptyWords P ∧ MPCP P) :=
  ⟨reduce, primrec_reduce.to_comp, nonemptyRules_and_sr_iff⟩

/-- **Reachability many-one reduces to PCP**, on rules with nonempty sides. -/
theorem manyOneReducible_sr_pcp :
    ManyOneReducible (fun I : List (Rule α) × List α × List α ↦ NonemptyRules I.1 ∧ SR I)
      (PCP (α := Sym (Sym α))) :=
  manyOneReducible_sr_mpcp.trans manyOneReducible_mpcp_pcp

end Computable

/-! ### Thue systems -/

section Thue

open Relation

/-- The **word problem** of the Thue system of `R`: on the instance `(R, x, y)`, are `x` and `y`
equivalent under the symmetric, reflexive and transitive closure of the rewriting steps? -/
def ThueWP (I : List (Rule α) × List α × List α) : Prop := EqvGen (Step I.1) I.2.1 I.2.2

theorem eqvGen_of_derives {R : List (Rule α)} {x y : List α} (h : Derives R x y) :
    EqvGen (Step R) x y := by
  induction h with
  | refl => exact EqvGen.refl _
  | tail _ hs ih => exact EqvGen.trans _ _ _ ih (EqvGen.rel _ _ hs)

theorem SR.thueWP {I : List (Rule α) × List α × List α} (h : SR I) : ThueWP I :=
  eqvGen_of_derives h

end Thue

end Cslib.Decidability.Rewriting
