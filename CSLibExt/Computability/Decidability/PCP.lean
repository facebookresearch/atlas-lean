/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Post correspondence problem: the modified problem reduces to PCP
-/
module

public import CSLibExt.Computability.Decidability.Basic
public import Mathlib.Computability.Reduce

/-!
# The Post correspondence problem: the modified problem reduces to PCP

An instance of the **Post correspondence problem** (PCP) is a finite list `P` of dominoes, each
a pair of words (top, bottom) over an alphabet `α`. A solution is a nonempty sequence of
dominoes from `P`, repetitions allowed, whose tops and bottoms concatenate to the same word.
In the **modified** problem (MPCP) a solution must also start with the first domino of `P`.

`toPCP P` is the classical reduction (Sipser, Theorem 5.15; Hopcroft–Motwani–Ullman,
Theorem 9.17). Over the alphabet `α` extended with `⋆` and `◇`:

* each domino `(t, b)` becomes `(⋆t, b⋆)`, where `⋆u` puts a star before every letter and
  `u⋆` after every letter;
* the first domino `(t₀, b₀)` also gives `(⋆t₀, ⋆b₀⋆)`, the only domino whose two words start
  with the same letter;
* the end domino `(⋆◇, ◇)` lets the top catch up with the trailing star.

**The reduction needs nonempty words.** If some domino of `P` has an empty bottom, `toPCP P`
can have a solution that starts with that domino, and then `P` may have no MPCP solution.
For example, `P = [(b, ab), (a, ε)]` has none, yet `(⋆a, ε), (⋆b, ⋆a⋆b⋆), (⋆◇, ◇)` solves
`toPCP P`. So `mpcp_iff_pcp_toPCP` assumes every domino has a nonempty top and bottom, which
holds for the instances that come from Turing machines. `manyOneReducible_mpcp_pcp`
packages this as a computable many-one reduction from MPCP on such instances to PCP.

## Main results

- `PCP`, `MPCP` : solvability of the two problems.
- `mpcp_iff_pcp_toPCP` : on instances with nonempty words, `MPCP P ↔ PCP (toPCP P)`.
- `manyOneReducible_mpcp_pcp` : MPCP on instances with nonempty words many-one reduces to PCP.
- `rePred_pcp`, `tm2Recognizable_pcp` : PCP is recursively enumerable, hence recognizable by a
  `FinTM2`: search all candidate sequences.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §5.2.
* J. E. Hopcroft, R. Motwani, J. D. Ullman, *Introduction to Automata Theory, Languages, and
  Computation*, 3rd ed., Pearson, 2006, §9.4.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability.Post

variable {α : Type*}

/-- **Domino (Post correspondence problem).** A domino over an alphabet $\alpha$ is a pair
$(t, b)$ of words over $\alpha$: its top word $t$ and its bottom word $b$. -/
abbrev Domino (α : Type*) := List α × List α

/-- **Top word of a sequence of dominoes.** For a sequence of dominoes
$(t_1, b_1), \ldots, (t_n, b_n)$, its top word is the concatenation $t_1 t_2 \cdots t_n$ of their
top words; the empty sequence has the empty top word. -/
def top (s : List (Domino α)) : List α := s.flatMap Prod.fst

/-- **Bottom word of a domino sequence.** For a sequence $s = d_1, \dots, d_k$ of dominoes, the
bottom word of $s$ is the concatenation $b_1 b_2 \cdots b_k$, where $b_i$ is the bottom word of
$d_i$. -/
def bottom (s : List (Domino α)) : List α := s.flatMap Prod.snd

/-- **PCP solution.** Let $P$ be a finite list of dominoes. A solution of $P$ is a nonempty
sequence $d_1, \dots, d_k$ of dominoes, each occurring in $P$ (repetitions allowed), such that the
concatenation of the top words of $d_1, \dots, d_k$ equals the concatenation of their bottom
words. -/
def IsSolution (P : List (Domino α)) (s : List (Domino α)) : Prop :=
  s ≠ [] ∧ (∀ d ∈ s, d ∈ P) ∧ top s = bottom s

/-- **The Post correspondence problem.** A list $P$ of dominoes is a solvable instance of the
Post correspondence problem when it has a PCP solution: a nonempty sequence of dominoes from $P$,
repetitions allowed, whose top words and bottom words concatenate to the same word. -/
def PCP (P : List (Domino α)) : Prop := ∃ s, IsSolution P s

/-- **The modified Post correspondence problem.** A list $P$ of dominoes has an MPCP solution
when $P$ is nonempty and some PCP solution of $P$ starts with the first domino of $P$. -/
def MPCP (P : List (Domino α)) : Prop :=
  ∃ d₀ s, P.head? = some d₀ ∧ IsSolution P (d₀ :: s)

/-- **Instances with nonempty words.** A list $P$ of dominoes has nonempty words when every
domino of $P$ has a nonempty top word and a nonempty bottom word. -/
def NonemptyWords (P : List (Domino α)) : Prop := ∀ d ∈ P, d.1 ≠ [] ∧ d.2 ≠ []

theorem top_append (s s' : List (Domino α)) : top (s ++ s') = top s ++ top s' :=
  List.flatMap_append

theorem bottom_append (s s' : List (Domino α)) : bottom (s ++ s') = bottom s ++ bottom s' :=
  List.flatMap_append

@[simp] theorem top_cons (d : Domino α) (s : List (Domino α)) : top (d :: s) = d.1 ++ top s :=
  List.flatMap_cons

@[simp] theorem bottom_cons (d : Domino α) (s : List (Domino α)) :
    bottom (d :: s) = d.2 ++ bottom s :=
  List.flatMap_cons

@[simp] theorem top_nil : top ([] : List (Domino α)) = [] := rfl

@[simp] theorem bottom_nil : bottom ([] : List (Domino α)) = [] := rfl

/-! ### The extended alphabet -/

/-- **The extended alphabet of the MPCP-to-PCP reduction.** For an alphabet $\alpha$, the extended
alphabet consists of the letters of $\alpha$ together with two new symbols: the star $\star$ and
the end marker $\diamond$.

It is represented so that it has a primitive recursive encoding whenever $\alpha$ has one. -/
abbrev Sym (α : Type*) := Option (Option α)

/-- **The alphabet inside the extended alphabet.** Each letter $a$ of the alphabet $\alpha$ is
regarded as a symbol of the extended alphabet of the MPCP-to-PCP reduction, which consists of the
letters of $\alpha$, the star $\star$ and the end marker $\diamond$. -/
abbrev letter (a : α) : Sym α := some (some a)

/-- **The star symbol.** The star $\star$ is the new symbol of the extended alphabet that is
neither a letter of $\alpha$ nor the end marker $\diamond$. -/
abbrev star : Sym α := some none

/-- **End marker.** The end marker $\diamond$ is the symbol of the extended alphabet of the
MPCP-to-PCP reduction that is neither a letter of $\alpha$ nor the star $\star$. -/
abbrev endMark : Sym α := none

/-- **A star before every letter.** Let $\star$ be the star of the extended alphabet. For a word
$u = a_1 a_2 \cdots a_n$ over $\alpha$, the word $\star u$ over the extended alphabet is
$\star a_1 \star a_2 \cdots \star a_n$, obtained by putting a star before every letter of $u$; the
empty word gives the empty word. -/
def starBefore (u : List α) : List (Sym α) := u.flatMap fun a ↦ [star, letter a]

/-- **A star after every letter.** Let $\star$ be the star of the extended alphabet. For a word
$u = a_1 a_2 \cdots a_n$ over $\alpha$, the word $u\star$ over the extended alphabet is
$a_1 \star a_2 \star \cdots a_n \star$, obtained by putting a star after every letter of $u$; the
empty word gives the empty word. -/
def starAfter (u : List α) : List (Sym α) := u.flatMap fun a ↦ [letter a, star]

/-- **Erasing stars and end markers.** For a word $w$ over the extended alphabet of the
MPCP-to-PCP reduction, this is the word over $\alpha$ obtained from $w$ by deleting every star
$\star$ and every end marker $\diamond$, keeping the letters of $\alpha$ in their order. -/
def letters (w : List (Sym α)) : List α := w.filterMap fun x ↦ x.bind id

@[simp] theorem letters_append (w w' : List (Sym α)) :
    letters (w ++ w') = letters w ++ letters w' :=
  List.filterMap_append

@[simp] theorem letters_starBefore (u : List α) : letters (starBefore u) = u := by
  induction u with
  | nil => rfl
  | cons a u ih => exact congrArg (a :: ·) ih

@[simp] theorem letters_starAfter (u : List α) : letters (starAfter u) = u := by
  induction u with
  | nil => rfl
  | cons a u ih => exact congrArg (a :: ·) ih

theorem starBefore_append_star (u : List α) :
    starBefore u ++ [star] = star :: starAfter u := by
  induction u with
  | nil => rfl
  | cons a u ih => exact congrArg (fun w ↦ star :: letter a :: w) ih

/-! ### The reduction -/

/-- **Starred image of a domino.** For a word $u$ over $\alpha$, write $\star u$ for the word over
the extended alphabet obtained by putting a star $\star$ before every letter of $u$, and $u\star$
for the word obtained by putting a star after every letter. A domino $(t, b)$ over $\alpha$ is sent
to the domino $(\star t, b\star)$ over the extended alphabet. -/
def mapDomino (d : Domino α) : Domino (Sym α) := (starBefore d.1, starAfter d.2)

/-- **The start domino of the MPCP-to-PCP reduction.** For a domino $(t, b)$ over an alphabet
$\alpha$, its start domino is the domino $(\star t, \star b \star)$ over the extended alphabet,
where $\star t$ puts the star $\star$ before every letter of $t$ and $b \star$ puts a star after
every letter of $b$, so that the bottom word gets one extra star in front. -/
def startDomino (d : Domino α) : Domino (Sym α) := (starBefore d.1, star :: starAfter d.2)

/-- **End domino of the MPCP-to-PCP reduction.** Over the alphabet $\alpha$ extended with the
star $\star$ and the end marker $\diamond$, the end domino is $(\star\diamond, \diamond)$: its top
word is $\star$ followed by $\diamond$, and its bottom word is $\diamond$. -/
def endDomino : Domino (Sym α) := ([star, endMark], [endMark])

/-- **The reduction from MPCP to PCP.** Write $\star$ for the star and $\diamond$ for the end
marker of the extended alphabet; for a word $u$ over $\alpha$, $\star u$ puts a star before every
letter of $u$ and $u \star$ puts a star after every letter of $u$. The empty list of dominoes is
sent to the empty list. A list $P = [d_0, d_1, \ldots, d_n]$ of dominoes over $\alpha$, with
$d_0 = (t_0, b_0)$, is sent to the following list of dominoes over the extended alphabet: first
the start domino $(\star t_0, \star b_0 \star)$, then the domino $(\star t, b \star)$ for each
domino $(t, b)$ of $P$ in order (including $d_0$), and last the end domino
$(\star \diamond, \diamond)$, whose top word is a star followed by the end marker. -/
def toPCP : List (Domino α) → List (Domino (Sym α))
  | [] => []
  | d₀ :: P => startDomino d₀ :: ((d₀ :: P).map mapDomino ++ [endDomino])

/-- **Erasing the markers from a domino.** For a domino $(t, b)$ over the extended alphabet, its
unmapping is the domino over $\alpha$ obtained by deleting every star $\star$ and every end marker
$\diamond$ from both $t$ and $b$, keeping the letters of $\alpha$ in order.

It reads a domino of the reduced PCP instance back as a domino over $\alpha$. -/
def unmap (d : Domino (Sym α)) : Domino α := (letters d.1, letters d.2)

@[simp] theorem unmap_mapDomino (d : Domino α) : unmap (mapDomino d) = d :=
  Prod.ext (letters_starBefore _) (letters_starAfter _)

@[simp] theorem unmap_startDomino (d : Domino α) : unmap (startDomino d) = d :=
  Prod.ext (letters_starBefore _) ((letters_append [star] _).trans (letters_starAfter _))

theorem letters_top (s : List (Domino (Sym α))) :
    letters (top s) = top (s.map unmap) := by
  induction s with
  | nil => rfl
  | cons d s ih => simp [ih, unmap]

theorem letters_bottom (s : List (Domino (Sym α))) :
    letters (bottom s) = bottom (s.map unmap) := by
  induction s with
  | nil => rfl
  | cons d s ih => simp [ih, unmap]

theorem top_map_mapDomino (s : List (Domino α)) :
    top (s.map mapDomino) = starBefore (top s) := by
  induction s with
  | nil => rfl
  | cons d s ih => simp [ih, mapDomino, starBefore]

theorem bottom_map_mapDomino (s : List (Domino α)) :
    bottom (s.map mapDomino) = starAfter (bottom s) := by
  induction s with
  | nil => rfl
  | cons d s ih => simp [ih, mapDomino, starAfter]

/-- Dominoes whose top and bottom are both empty contribute nothing. -/
private def Keep (d : Domino α) : Bool := !(d.1.isEmpty && d.2.isEmpty)

private theorem top_filter_keep (s : List (Domino α)) : top (s.filter Keep) = top s := by
  induction s with
  | nil => rfl
  | cons d s ih =>
    by_cases h : Keep d = true
    · simp [h, ih]
    · have hk : d.1 = [] ∧ d.2 = [] := by simpa [Keep] using h
      simp [h, ih, hk.1]

private theorem bottom_filter_keep (s : List (Domino α)) : bottom (s.filter Keep) = bottom s := by
  induction s with
  | nil => rfl
  | cons d s ih =>
    by_cases h : Keep d = true
    · simp [h, ih]
    · have hk : d.1 = [] ∧ d.2 = [] := by simpa [Keep] using h
      simp [h, ih, hk.2]

theorem mem_toPCP {d₀ : Domino α} {P : List (Domino α)} {d : Domino (Sym α)} :
    d ∈ toPCP (d₀ :: P) ↔
      d = startDomino d₀ ∨ (∃ e ∈ d₀ :: P, mapDomino e = d) ∨ d = endDomino := by
  simp only [toPCP, List.mem_cons, List.mem_append, List.mem_map, List.mem_nil_iff, or_false]

/-! ### Correctness -/

/-- **An MPCP solution gives a PCP solution of the reduced instance.** If a list $P$ of dominoes
has an MPCP solution, then the image of $P$ under the reduction from MPCP to PCP has a PCP
solution. -/
theorem pcp_toPCP_of_mpcp {P : List (Domino α)} (h : MPCP P) : PCP (toPCP P) := by
  obtain ⟨d₀, s, hd₀, -, hmem, heq⟩ := h
  cases P with
  | nil => cases hd₀
  | cons d P =>
    obtain rfl : d = d₀ := Option.some.inj hd₀
    refine ⟨startDomino d :: (s.map mapDomino ++ [endDomino]), List.cons_ne_nil _ _, ?_, ?_⟩
    · intro e he
      rw [mem_toPCP]
      simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_nil_iff, or_false] at he
      rcases he with rfl | ⟨e', he', rfl⟩ | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨e', hmem e' (List.mem_cons_of_mem _ he'), rfl⟩)
      · exact Or.inr (Or.inr rfl)
    · simp only [top_cons, bottom_cons] at heq
      simp only [top_cons, bottom_cons, top_append, bottom_append, top_map_mapDomino,
        bottom_map_mapDomino, startDomino, endDomino, top_cons, bottom_cons, top_nil,
        bottom_nil, List.append_nil]
      have hT : starBefore d.1 ++ starBefore (top s) = starBefore (d.1 ++ top s) :=
        (List.flatMap_append).symm
      have hB : starAfter d.2 ++ starAfter (bottom s) = starAfter (d.2 ++ bottom s) :=
        (List.flatMap_append).symm
      rw [← List.append_assoc, hT, List.cons_append, ← List.append_assoc, hB, heq,
        show ([star, endMark] : List (Sym α)) = [star] ++ [endMark] from rfl,
        ← List.append_assoc, starBefore_append_star, List.cons_append]

/-- The first symbols of the two words of a domino of `toPCP P` other than the start domino
differ, when `P` has nonempty words. -/
private theorem head_ne_of_ne_start {d₀ : Domino α} {P : List (Domino α)}
    (hP : NonemptyWords (d₀ :: P)) {d : Domino (Sym α)} (hd : d ∈ toPCP (d₀ :: P))
    (hne : d ≠ startDomino d₀) :
    ∃ x y, x ≠ y ∧ (∃ u, d.1 = x :: u) ∧ ∃ v, d.2 = y :: v := by
  rcases mem_toPCP.mp hd with rfl | ⟨e, he, rfl⟩ | rfl
  · exact absurd rfl hne
  · obtain ⟨h₁, h₂⟩ := hP e he
    obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil h₁
    obtain ⟨b, u, hu⟩ := List.exists_cons_of_ne_nil h₂
    refine ⟨star, letter b, by simp, ⟨letter a :: starBefore t, ?_⟩,
      ⟨star :: starAfter u, ?_⟩⟩
    · simp [mapDomino, ht, starBefore]
    · simp [mapDomino, hu, starAfter]
  · exact ⟨star, endMark, by simp, ⟨[endMark], rfl⟩, ⟨[], rfl⟩⟩

/-- **On instances with nonempty words, a PCP solution of the reduced instance gives an MPCP
solution.** Let $P$ be a list of dominoes in which every domino has a nonempty top and a nonempty
bottom. If the image of $P$ under the reduction from MPCP to PCP has a PCP solution, then $P$ has
an MPCP solution. -/
theorem mpcp_of_pcp_toPCP {P : List (Domino α)} (hP : NonemptyWords P) (h : PCP (toPCP P)) :
    MPCP P := by
  obtain ⟨s', hne, hmem, heq⟩ := h
  cases P with
  | nil =>
    obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact absurd (hmem d List.mem_cons_self) (by simp [toPCP])
  | cons d₀ P =>
    obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hstart : d = startDomino d₀ := by
      by_contra hd
      obtain ⟨x, y, hxy, ⟨u, hu⟩, ⟨v, hv⟩⟩ :=
        head_ne_of_ne_start hP (hmem d List.mem_cons_self) hd
      simp only [top_cons, bottom_cons, hu, hv, List.cons_append, List.cons.injEq] at heq
      exact hxy heq.1
    subst hstart
    refine ⟨d₀, (rest.map unmap).filter Keep, rfl, List.cons_ne_nil _ _, ?_, ?_⟩
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact List.mem_cons_self
      · obtain ⟨he, hkeep⟩ := List.mem_filter.mp he
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        rcases mem_toPCP.mp (hmem e' (List.mem_cons_of_mem _ he')) with
          rfl | ⟨e'', he'', rfl⟩ | rfl
        · simp
        · simpa using he''
        · simp [Keep, unmap, endDomino, letters] at hkeep
    · have h' := congrArg letters heq
      rw [letters_top, letters_bottom] at h'
      simp only [List.map_cons, unmap_startDomino, top_cons, bottom_cons] at h'
      simpa only [top_cons, bottom_cons, top_filter_keep, bottom_filter_keep] using h'

/-- **MPCP reduces to PCP on instances with nonempty words.** Let $P$ be a list of dominoes over
an alphabet $\alpha$ in which every domino has a nonempty top and a nonempty bottom. Then $P$ has
an MPCP solution if and only if the image of $P$ under the reduction from MPCP to PCP, an
instance over $\alpha$ extended with a star and an end marker, has a PCP solution. -/
theorem mpcp_iff_pcp_toPCP {P : List (Domino α)} (hP : NonemptyWords P) :
    MPCP P ↔ PCP (toPCP P) :=
  ⟨pcp_toPCP_of_mpcp, mpcp_of_pcp_toPCP hP⟩

/-! ### The many-one reduction -/

/-- **Boolean test for nonempty words.** For a list $P$ of dominoes, this Boolean test returns
true exactly when every domino of $P$ has a nonempty top and a nonempty bottom. -/
def nonemptyWordsB (P : List (Domino α)) : Bool := P.all fun d ↦ !d.1.isEmpty && !d.2.isEmpty

theorem nonemptyWordsB_iff {P : List (Domino α)} : nonemptyWordsB P = true ↔ NonemptyWords P := by
  simp [nonemptyWordsB, NonemptyWords]

/-- **The total reduction from MPCP to PCP.** For a list $P$ of dominoes, the total reduction
sends $P$ to its image under the reduction from MPCP to PCP when every domino of $P$ has a
nonempty top and a nonempty bottom, and to the empty instance, which has no PCP solution,
otherwise. -/
def reduce (P : List (Domino α)) : List (Domino (Sym α)) :=
  cond (nonemptyWordsB P) (toPCP P) []

theorem not_pcp_nil : ¬PCP ([] : List (Domino α)) := by
  rintro ⟨s, hne, hmem, -⟩
  obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact absurd (hmem d List.mem_cons_self) (by simp)

theorem nonemptyWords_and_mpcp_iff_pcp_reduce (P : List (Domino α)) :
    NonemptyWords P ∧ MPCP P ↔ PCP (reduce P) := by
  by_cases h : NonemptyWords P
  · simp [reduce, nonemptyWordsB_iff.mpr h, h, mpcp_iff_pcp_toPCP h]
  · have hb : nonemptyWordsB P = false :=
      Bool.eq_false_iff.mpr fun hh ↦ h (nonemptyWordsB_iff.mp hh)
    simp [reduce, hb, h, not_pcp_nil]

section Computable

variable [Primcodable α]

theorem primrec_starBefore : Primrec (starBefore (α := α)) :=
  Primrec.list_flatMap Primrec.id ((Primrec.list_cons.comp (Primrec.const star)
    (Primrec.list_cons.comp (Primrec.option_some.comp (Primrec.option_some.comp Primrec.snd))
      (Primrec.const []))).to₂)

theorem primrec_starAfter : Primrec (starAfter (α := α)) :=
  Primrec.list_flatMap Primrec.id ((Primrec.list_cons.comp
    (Primrec.option_some.comp (Primrec.option_some.comp Primrec.snd))
    (Primrec.list_cons.comp (Primrec.const star) (Primrec.const []))).to₂)

theorem primrec_toPCP : Primrec (toPCP (α := α)) := by
  have hmap : Primrec (mapDomino (α := α)) :=
    Primrec.pair (primrec_starBefore.comp Primrec.fst) (primrec_starAfter.comp Primrec.snd)
  have hstart : Primrec (startDomino (α := α)) :=
    Primrec.pair (primrec_starBefore.comp Primrec.fst)
      (Primrec.list_cons.comp (Primrec.const star) (primrec_starAfter.comp Primrec.snd))
  have hcons : Primrec₂ fun (P : List (Domino α)) (p : Domino α × List (Domino α)) ↦
      startDomino p.1 :: (P.map mapDomino ++ [endDomino]) :=
    Primrec.list_cons.comp (hstart.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.list_append.comp (Primrec.list_map Primrec.fst (hmap.comp Primrec.snd).to₂)
        (Primrec.const [endDomino]))
  exact (Primrec.list_casesOn Primrec.id (Primrec.const []) hcons).of_eq fun P ↦ by
    cases P <;> rfl

/-- **The nonempty-words test is primitive recursive.** For an alphabet $\alpha$ with a
primitive recursive coding, the Boolean test of whether every domino of a list over $\alpha$ has
a nonempty top and a nonempty bottom is a primitive recursive function of the list. -/
theorem primrec_nonemptyWordsB : Primrec (nonemptyWordsB (α := α)) := by
  have hE : ∀ {β : Type _} [Primcodable β], Primrec fun l : List β ↦ l.isEmpty := fun {β} _ ↦
    (Primrec.list_casesOn Primrec.id (Primrec.const true)
      (Primrec.const false : Primrec fun _ : List β × (β × List β) ↦ false).to₂).of_eq
        fun l ↦ by cases l <;> rfl
  have hd : Primrec fun d : Domino α ↦ !d.1.isEmpty && !d.2.isEmpty :=
    Primrec.and.comp (Primrec.not.comp (hE.comp Primrec.fst))
      (Primrec.not.comp (hE.comp Primrec.snd))
  refine (Primrec.list_foldr Primrec.id (Primrec.const true)
    (Primrec.and.comp (hd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun P ↦ ?_
  simp only [id, nonemptyWordsB]
  induction P with
  | nil => rfl
  | cons d P ih => simp only [List.foldr_cons, List.all_cons, ih]

theorem primrec_reduce : Primrec (reduce (α := α)) := by
  have hb := primrec_nonemptyWordsB (α := α)
  exact Primrec.cond hb primrec_toPCP (Primrec.const [])

/-- **MPCP many-one reduces to PCP.** Let $\alpha$ be an alphabet with a primitive recursive
coding, and let $\alpha'$ be $\alpha$ extended with two new symbols, the star and the end marker.
There is a computable function $f$ from finite lists of dominoes over $\alpha$ to finite lists of
dominoes over $\alpha'$ such that, for every list $P$ of dominoes over $\alpha$, $f(P)$ has a PCP
solution if and only if both every domino of $P$ has a nonempty top word and a nonempty bottom
word, and $P$ has an MPCP solution. -/
theorem manyOneReducible_mpcp_pcp :
    ManyOneReducible (fun P : List (Domino α) ↦ NonemptyWords P ∧ MPCP P)
      (PCP (α := Sym α)) :=
  ⟨reduce, primrec_reduce.to_comp, nonemptyWords_and_mpcp_iff_pcp_reduce⟩

end Computable

/-! ### PCP is recognizable -/

section Recognizable

variable [Primcodable α]

/-- **Boolean check for PCP solutions.** Let $\alpha$ be an alphabet with a primitive recursive
coding and decidable equality, and let $P$ and $s$ be lists of dominoes over $\alpha$. The Boolean
solution check of $s$ for $P$ is true exactly when $s$ is nonempty, every domino of $s$ occurs in
$P$, and the top word of $s$ equals the bottom word of $s$, and it is false otherwise. -/
def isSolutionB [DecidableEq α] (P s : List (Domino α)) : Bool :=
  !s.isEmpty && s.all (fun d ↦ decide (d ∈ P)) && decide (top s = bottom s)

omit [Primcodable α] in
theorem isSolutionB_iff [DecidableEq α] {P s : List (Domino α)} :
    isSolutionB P s = true ↔ IsSolution P s := by
  simp [isSolutionB, IsSolution, and_assoc]

private theorem primrec_isEmpty {β : Type*} [Primcodable β] :
    Primrec fun l : List β ↦ l.isEmpty :=
  (Primrec.list_casesOn Primrec.id (Primrec.const true)
    (Primrec.const false : Primrec fun _ : List β × (β × List β) ↦ false).to₂).of_eq
      fun l ↦ by cases l <;> rfl

theorem primrec₂_isSolutionB [DecidableEq α] : Primrec₂ (isSolutionB (α := α)) := by
  have hmem : Primrec₂ fun (P : List (Domino α)) (d : Domino α) ↦ decide (d ∈ P) := by
    have h := (Primrec.nat_lt.comp (Primrec.list_idxOf.comp Primrec.snd Primrec.fst)
      ((Primrec.list_length (α := Domino α)).comp Primrec.fst)).decide
    exact h.of_eq fun p ↦ by simp [List.idxOf_lt_length_iff]
  have hall : Primrec₂ fun (P s : List (Domino α)) ↦ s.all fun d ↦ decide (d ∈ P) := by
    refine (Primrec.list_foldr Primrec.snd (Primrec.const true)
      (Primrec.and.comp (hmem.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun p ↦ ?_
    obtain ⟨P, s⟩ := p
    simp only
    induction s with
    | nil => rfl
    | cons d s ih => simp only [List.foldr_cons, List.all_cons, ih]
  have htop : Primrec (top (α := α)) :=
    Primrec.list_flatMap Primrec.id (Primrec.fst.comp Primrec.snd).to₂
  have hbot : Primrec (bottom (α := α)) :=
    Primrec.list_flatMap Primrec.id (Primrec.snd.comp Primrec.snd).to₂
  exact Primrec.and.comp (Primrec.and.comp (Primrec.not.comp (primrec_isEmpty.comp Primrec.snd))
    hall) (Primrec.eq.comp (htop.comp Primrec.snd) (hbot.comp Primrec.snd)).decide

/-- **PCP is recursively enumerable.** For an alphabet $\alpha$ with a primitive recursive
coding, the set of lists of dominoes over $\alpha$ that have a PCP solution is recursively
enumerable.

The proof searches all candidate sequences. -/
theorem rePred_pcp : REPred (PCP (α := α)) := by
  classical
  let q : List (Domino α) → ℕ → Bool := fun P k ↦
    (Encodable.decode (α := List (Domino α)) k).elim false (isSolutionB P)
  have hq : Primrec₂ q :=
    (Primrec.option_casesOn (Primrec.decode.comp Primrec.snd) (Primrec.const false)
      (primrec₂_isSolutionB.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
        fun p ↦ by cases h : Encodable.decode (α := List (Domino α)) p.2 <;> simp [q, h]
  have hp : Partrec fun P ↦ Nat.rfind fun k ↦ Part.some (q P k) :=
    Partrec.rfind (hq.to_comp.partrec₂)
  refine hp.dom_re.of_eq fun P ↦ ?_
  refine Nat.rfind_dom.trans ?_
  simp only [Part.mem_some_iff, Part.some_dom, implies_true, and_true]
  constructor
  · rintro ⟨k, hk⟩
    cases h : Encodable.decode (α := List (Domino α)) k with
    | none => simp [q, h] at hk
    | some s => exact ⟨s, isSolutionB_iff.mp (by simpa [q, h] using hk.symm)⟩
  · rintro ⟨s, hs⟩
    exact ⟨Encodable.encode s, by simp [q, Encodable.encodek, isSolutionB_iff.mpr hs]⟩

/-- **PCP is Turing-recognizable.** For every alphabet $\alpha$ with a primitive recursive
encoding, there is a multi-stack Turing machine that, started on the binary encoding of a list
$P$ of dominoes over $\alpha$, halts exactly when $P$ has a PCP solution. -/
theorem tm2Recognizable_pcp : TM2Recognizable (PCP (α := α)) :=
  tm2Recognizable_iff_rePred.mpr rePred_pcp

end Recognizable

end Cslib.Decidability.Post
