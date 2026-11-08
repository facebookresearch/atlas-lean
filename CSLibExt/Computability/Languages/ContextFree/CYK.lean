/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The CYK recognizer
-/
module

public import CSLibExt.Computability.Languages.ContextFree.ChomskyNormalForm

/-!
# The Cocke–Younger–Kasami recognizer

For a grammar in Chomsky normal form (`Cslib.Language.IsChomskyNormalForm`) with decidable
equality on terminals and nonterminals, `Cslib.Language.cykAccepts g w` decides whether `w` is in
the language of `g`, by the CYK recurrence: a nonterminal `A` derives a nonempty word `w` when
some production `A → a` has `w = [a]`, or some production `A → B C` and some split
`w = u ++ v` into nonempty parts have `B` deriving `u` and `C` deriving `v`. The recognizer fills
a table with one cell per factor of `w`, shortest factors first, so each cell is computed once
from the cells of shorter factors (polynomially many steps in `|w|` for a fixed grammar, rather
than the exponential unshared recursion `cykCell`). No `Fintype` instance on nonterminals is
needed: cells are images of the finite production set.

## Main definitions

* `Cslib.Language.cykCellFrom g f w`: one step of the recurrence, from cells `f` of the parts.
* `Cslib.Language.cykCell g n w`: the recurrence run to depth `n`, without sharing.
* `Cslib.Language.cykTable g w l`: the table of all factors of `w` of length `1, …, l`.
* `Cslib.Language.cykAccepts g w`: the recognizer; the empty word is handled by the production
  `S → ε`.

## Main results

* `Cslib.Language.yields_nonterminal_iff_of_ne_nil`: under Chomsky normal form, a nonterminal
  yields a nonempty word through a terminal production or a binary production whose two
  nonterminals yield nonempty parts.
* `Cslib.Language.mem_cykCellFrom_iff`: one step of the recurrence is correct when the cells of
  the parts are.
* `Cslib.Language.mem_cykCell_iff`: for a nonempty word and depth at least its length, the cell
  is exactly the set of nonterminals yielding the word.
* `Cslib.Language.cykTable_spec`: every cell of the table is correct and every factor of `w` of
  the covered lengths has an entry.
* `Cslib.Language.cykAccepts_iff`: `cykAccepts g w = true ↔ w ∈ g.language`.
-/

@[expose] public section

namespace Cslib.Language

variable {T : Type*} {g : ContextFreeGrammar T}

/-! ## Yields under Chomsky normal form -/

theorem yields_nonterminal_singleton_iff {A : g.NT} {w : List T} :
    Yields g [.nonterminal A] w ↔ ∃ r ∈ g.rules, r.input = A ∧ Yields g r.output w := by
  constructor
  · intro h
    cases h with
    | nonterminal hr hout hrest =>
        cases hrest
        exact ⟨_, hr, rfl, by simpa using hout⟩
  · rintro ⟨r, hr, rfl, h⟩
    exact yields_of_rule hr h

theorem yields_nil_iff {w : List T} : Yields g [] w ↔ w = [] := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact Yields.nil

theorem yields_terminal_singleton_iff {a : T} {w : List T} :
    Yields g [.terminal a] w ↔ w = [a] := by
  constructor
  · intro h
    cases h with
    | terminal _ h => rw [yields_nil_iff.1 h]
  · rintro rfl
    exact Yields.terminal a Yields.nil

theorem yields_pair_iff {B C : g.NT} {w : List T} :
    Yields g [.nonterminal B, .nonterminal C] w ↔
      ∃ w₁ w₂, w = w₁ ++ w₂ ∧ Yields g [.nonterminal B] w₁ ∧ Yields g [.nonterminal C] w₂ := by
  constructor
  · intro h
    exact Yields.append_inv (u := [.nonterminal B]) (v := [.nonterminal C]) h
  · rintro ⟨w₁, w₂, rfl, h₁, h₂⟩
    exact Yields.append (u := [.nonterminal B]) (v := [.nonterminal C]) h₁ h₂

/-- Under Chomsky normal form, a nonterminal occurring in a production output has no empty
production: such a production would have the initial nonterminal on the left, which then occurs
in an output while an empty production exists. -/
theorem no_empty_rule_of_mem_output (hg : IsChomskyNormalForm g) {r : ContextFreeRule T g.NT}
    (hr : r ∈ g.rules) {B : g.NT} (hB : Symbol.nonterminal B ∈ r.output) :
    ¬ ∃ r' ∈ g.rules, r'.input = B ∧ r'.output = [] := by
  rintro ⟨r', hr', hin, hout⟩
  have hBinit : B = g.initial := by
    rcases hg.1 r' hr' with ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · rw [hout] at h
      simp at h
    · rw [hout] at h
      simp at h
    · rw [← hin, h]
  rcases hg.2 with h | h
  · exact h r hr (hBinit ▸ hB)
  · exact h r' hr' hout

/-- Under Chomsky normal form, every symbol of a form yielding the empty word is a nonterminal
with an empty production. -/
theorem empty_rule_of_yields_nil (hg : IsChomskyNormalForm g) {u : List (Symbol T g.NT)}
    {w : List T} (h : Yields g u w) (hw : w = []) :
    ∀ s ∈ u, ∃ B, s = .nonterminal B ∧ ∃ r ∈ g.rules, r.input = B ∧ r.output = [] := by
  induction h with
  | nil => simp
  | terminal a _ _ => simp at hw
  | @nonterminal r hr u w₁ w₂ hout hrest ihout ihrest =>
      obtain ⟨hw₁, hw₂⟩ := List.append_eq_nil_iff.1 hw
      intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · refine ⟨_, rfl, ?_⟩
        rcases hg.1 r hr with ⟨B, C, hBC⟩ | ⟨a, ha⟩ | ⟨hnil, -⟩
        · exfalso
          have hBmem : Symbol.nonterminal B ∈ r.output := by
            rw [hBC]
            exact List.mem_cons_self
          obtain ⟨B', hB', hrule⟩ := ihout hw₁ _ hBmem
          obtain rfl : B = B' := Symbol.nonterminal.inj hB'
          exact no_empty_rule_of_mem_output hg hr hBmem hrule
        · exfalso
          obtain ⟨B', hB', -⟩ := ihout hw₁ (.terminal a) (by rw [ha]; exact List.mem_cons_self)
          cases hB'
        · exact ⟨r, hr, rfl, hnil⟩
      · exact ihrest hw₂ s hs

/-- **Shape of yields under Chomsky normal form.** A nonterminal yields a nonempty word exactly
through a production `A → a` with `w = [a]`, or a production `A → B C` with `B` and `C`
yielding the two nonempty parts of a split of `w`. -/
theorem yields_nonterminal_iff_of_ne_nil (hg : IsChomskyNormalForm g) {A : g.NT} {w : List T}
    (hw : w ≠ []) :
    Yields g [.nonterminal A] w ↔ ∃ r ∈ g.rules, r.input = A ∧
      ((∃ a, r.output = [.terminal a] ∧ w = [a]) ∨
        ∃ B C w₁ w₂, r.output = [.nonterminal B, .nonterminal C] ∧ w = w₁ ++ w₂ ∧
          w₁ ≠ [] ∧ w₂ ≠ [] ∧ Yields g [.nonterminal B] w₁ ∧ Yields g [.nonterminal C] w₂) := by
  rw [yields_nonterminal_singleton_iff]
  refine exists_congr fun r => and_congr_right fun hr => and_congr_right fun _ => ?_
  rcases hg.1 r hr with ⟨B, C, hBC⟩ | ⟨a, ha⟩ | ⟨hnil, -⟩
  · rw [hBC, yields_pair_iff]
    constructor
    · rintro ⟨w₁, w₂, rfl, h₁, h₂⟩
      refine Or.inr ⟨B, C, w₁, w₂, rfl, rfl, ?_, ?_, h₁, h₂⟩
      · rintro rfl
        have hmem : Symbol.nonterminal B ∈ r.output := by rw [hBC]; exact List.mem_cons_self
        obtain ⟨B', hB', hrule⟩ := empty_rule_of_yields_nil hg h₁ rfl _ List.mem_cons_self
        obtain rfl : B = B' := Symbol.nonterminal.inj hB'
        exact no_empty_rule_of_mem_output hg hr hmem hrule
      · rintro rfl
        have hmem : Symbol.nonterminal C ∈ r.output := by rw [hBC]; simp
        obtain ⟨C', hC', hrule⟩ := empty_rule_of_yields_nil hg h₂ rfl _ List.mem_cons_self
        obtain rfl : C = C' := Symbol.nonterminal.inj hC'
        exact no_empty_rule_of_mem_output hg hr hmem hrule
    · rintro (⟨a, ha, -⟩ | ⟨B', C', w₁, w₂, hBC', rfl, -, -, h₁, h₂⟩)
      · simp at ha
      · simp only [List.cons.injEq, Symbol.nonterminal.injEq, and_true] at hBC'
        obtain ⟨rfl, rfl⟩ := hBC'
        exact ⟨w₁, w₂, rfl, h₁, h₂⟩
  · rw [ha, yields_terminal_singleton_iff]
    constructor
    · intro h
      exact Or.inl ⟨a, rfl, h⟩
    · rintro (⟨a', ha', h⟩ | ⟨B, C, -, -, h, -⟩)
      · simp only [List.cons.injEq, Symbol.terminal.injEq, and_true] at ha'
        rw [h, ha']
      · simp at h
  · rw [hnil, yields_nil_iff]
    constructor
    · intro h
      exact absurd h hw
    · rintro (⟨a, h, -⟩ | ⟨B, C, -, -, h, -⟩) <;> simp at h

/-! ## The recognizer -/

variable [DecidableEq T] [DecidableEq g.NT]

/-- Whether a production output fits `w`, given the cells `f` of shorter words: `[a]` fits
`[a]`, and `[B, C]` fits when some split of `w` into nonempty parts has `B` in the cell of the
first part and `C` in the cell of the second. -/
def cykFits (f : List T → Finset g.NT) (w : List T) : List (Symbol T g.NT) → Bool
  | [.terminal a] => decide (w = [a])
  | [.nonterminal B, .nonterminal C] =>
      (List.range w.length).any fun i =>
        decide (0 < i) && decide (B ∈ f (w.take i)) && decide (C ∈ f (w.drop i))
  | _ => false

variable (g) in
/-- The cell of `w` given the cells `f` of its parts: the left-hand sides of the productions
whose outputs fit `w`. -/
def cykCellFrom (f : List T → Finset g.NT) (w : List T) : Finset g.NT :=
  (g.rules.filter fun r => cykFits f w r.output = true).image ContextFreeRule.input

theorem cykFits_pair_iff {f : List T → Finset g.NT} {w : List T} {B C : g.NT} :
    cykFits f w [.nonterminal B, .nonterminal C] = true ↔
      ∃ i < w.length, 0 < i ∧ B ∈ f (w.take i) ∧ C ∈ f (w.drop i) := by
  simp [cykFits, List.any_eq_true, and_assoc]

/-- **The CYK step.** If the cells `f` are correct on the two parts of every split of a nonempty
word `w` into nonempty parts, the cell built from them holds exactly the nonterminals yielding
`w`. -/
theorem mem_cykCellFrom_iff (hg : IsChomskyNormalForm g) {f : List T → Finset g.NT}
    {w : List T} (hw : w ≠ [])
    (hf : ∀ i, 0 < i → i < w.length → ∀ B,
      (B ∈ f (w.take i) ↔ Yields g [.nonterminal B] (w.take i)) ∧
      (B ∈ f (w.drop i) ↔ Yields g [.nonterminal B] (w.drop i)))
    {A : g.NT} : A ∈ cykCellFrom g f w ↔ Yields g [.nonterminal A] w := by
  rw [yields_nonterminal_iff_of_ne_nil hg hw]
  simp only [cykCellFrom, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨r, ⟨hr, hfit⟩, rfl⟩
    refine ⟨r, hr, rfl, ?_⟩
    rcases hg.1 r hr with ⟨B, C, hBC⟩ | ⟨a, ha⟩ | ⟨hnil, -⟩
    · rw [hBC, cykFits_pair_iff] at hfit
      obtain ⟨i, hilen, hi0, hB, hC⟩ := hfit
      have htake : w.take i ≠ [] := by
        rw [Ne, List.take_eq_nil_iff]
        rintro (h | h)
        · omega
        · exact hw h
      have hdrop : w.drop i ≠ [] := by
        rw [Ne, List.drop_eq_nil_iff]
        omega
      exact Or.inr ⟨B, C, w.take i, w.drop i, hBC, (List.take_append_drop i w).symm,
        htake, hdrop, ((hf i hi0 hilen B).1).1 hB, ((hf i hi0 hilen C).2).1 hC⟩
    · rw [ha] at hfit
      exact Or.inl ⟨a, ha, by simpa [cykFits] using hfit⟩
    · rw [hnil] at hfit
      simp [cykFits] at hfit
  · rintro ⟨r, hr, rfl, (⟨a, ha, rfl⟩ | ⟨B, C, w₁, w₂, hBC, rfl, h₁, h₂, hB, hC⟩)⟩
    · exact ⟨r, ⟨hr, by simp [ha, cykFits]⟩, rfl⟩
    · refine ⟨r, ⟨hr, ?_⟩, rfl⟩
      rw [hBC, cykFits_pair_iff]
      have hl₁ : 0 < w₁.length := List.length_pos_iff.2 h₁
      have hl₂ : 0 < w₂.length := List.length_pos_iff.2 h₂
      have hlt : w₁.length < (w₁ ++ w₂).length := by simp; omega
      refine ⟨w₁.length, hlt, hl₁, ?_, ?_⟩
      · have h := ((hf w₁.length hl₁ hlt B).1).2
        rw [List.take_left] at h ⊢
        exact h hB
      · have h := ((hf w₁.length hl₁ hlt C).2).2
        rw [List.drop_left] at h ⊢
        exact h hC

variable (g) in
/-- The CYK recurrence run to depth `n`, without sharing: the cell of `w` from the depth-`n - 1`
cells of its parts. -/
def cykCell : ℕ → List T → Finset g.NT
  | 0, _ => ∅
  | n + 1, w => cykCellFrom g (cykCell n) w

/-- **Correctness of the recurrence.** For a nonempty word and a depth at least its length, the
cell holds exactly the nonterminals that yield the word. -/
theorem mem_cykCell_iff (hg : IsChomskyNormalForm g) :
    ∀ (n : ℕ) {A : g.NT} {w : List T}, w ≠ [] → w.length ≤ n →
      (A ∈ cykCell g n w ↔ Yields g [.nonterminal A] w) := by
  intro n
  induction n with
  | zero =>
      intro A w hw hlen
      exact absurd (List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)) hw
  | succ n ih =>
      intro A w hw hlen
      refine mem_cykCellFrom_iff hg hw fun i hi0 hilen B => ⟨ih ?_ ?_, ih ?_ ?_⟩
      · rw [Ne, List.take_eq_nil_iff]
        rintro (h | h)
        · omega
        · exact hw h
      · simp only [List.length_take]; omega
      · rw [Ne, List.drop_eq_nil_iff]; omega
      · simp only [List.length_drop]; omega

/-! ## The table -/

/-- The cell recorded for `u` in a table of words and cells (the first entry for `u`). -/
def cykLookup (tbl : List (List T × Finset g.NT)) (u : List T) : Finset g.NT :=
  ((tbl.find? fun e => e.1 = u).map Prod.snd).getD ∅

variable (g) in
/-- The CYK table of `w` up to length `l`: one entry for each factor of `w` of length `1, …, l`,
each cell computed from the entries of the shorter factors. -/
def cykTable (w : List T) : ℕ → List (List T × Finset g.NT)
  | 0 => []
  | l + 1 =>
      let tbl := cykTable w l
      tbl ++ (List.range (w.length - l)).map fun i =>
        let u := (w.drop i).take (l + 1)
        (u, cykCellFrom g (cykLookup tbl) u)

/-- All recorded cells are correct. -/
def CykTableCorrect (tbl : List (List T × Finset g.NT)) : Prop :=
  ∀ e ∈ tbl, e.1 ≠ [] → ∀ B, B ∈ e.2 ↔ Yields g [.nonterminal B] e.1

omit [DecidableEq g.NT] in
theorem mem_cykLookup_iff {tbl : List (List T × Finset g.NT)} (htbl : CykTableCorrect tbl)
    {u : List T} (hu : u ≠ []) (hkey : ∃ e ∈ tbl, e.1 = u) {B : g.NT} :
    B ∈ cykLookup tbl u ↔ Yields g [.nonterminal B] u := by
  obtain ⟨e, he, rfl⟩ := hkey
  have hsome : (tbl.find? fun e' => decide (e'.1 = e.1)).isSome :=
    List.find?_isSome.2 ⟨e, he, decide_eq_true rfl⟩
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 hsome
  have hmem := List.mem_of_find?_eq_some he'
  have hkey' : e'.1 = e.1 :=
    of_decide_eq_true
      (List.find?_some (p := fun x : List T × Finset g.NT => decide (x.1 = e.1)) he')
  rw [cykLookup, he', Option.map_some, Option.getD_some, ← hkey']
  exact htbl e' hmem (hkey' ▸ hu) B

/-- **Correctness of the table**: its cells are correct, and it records every factor of `w` of
length `1, …, l`. -/
theorem cykTable_spec (hg : IsChomskyNormalForm g) (w : List T) :
    ∀ l, CykTableCorrect (cykTable g w l) ∧
      ∀ j m, 0 < m → m ≤ l → j + m ≤ w.length →
        ∃ e ∈ cykTable g w l, e.1 = (w.drop j).take m := by
  intro l
  induction l with
  | zero => exact ⟨fun e he => by simp [cykTable] at he, fun j m h0 hm => by omega⟩
  | succ l ih =>
      obtain ⟨hcorr, hkeys⟩ := ih
      have hnew : ∀ i, i < w.length - l → ∀ B,
          B ∈ cykCellFrom g (cykLookup (cykTable g w l)) ((w.drop i).take (l + 1)) ↔
            Yields g [.nonterminal B] ((w.drop i).take (l + 1)) := by
        intro i hi B
        have hlen : ((w.drop i).take (l + 1)).length = l + 1 := by simp; omega
        have hne : (w.drop i).take (l + 1) ≠ [] := by
          intro h
          rw [h] at hlen
          simp at hlen
        refine mem_cykCellFrom_iff hg hne fun k hk0 hklen C => ⟨?_, ?_⟩
        · rw [hlen] at hklen
          have hk : ((w.drop i).take (l + 1)).take k = (w.drop i).take k := by
            rw [List.take_take]
            congr 1
            omega
          rw [hk]
          refine mem_cykLookup_iff hcorr ?_ (hkeys i k hk0 (by omega) (by omega))
          intro h
          have := congrArg List.length h
          simp at this
          omega
        · rw [hlen] at hklen
          have hk : ((w.drop i).take (l + 1)).drop k = (w.drop (i + k)).take (l + 1 - k) := by
            rw [List.drop_take, List.drop_drop]
          rw [hk]
          refine mem_cykLookup_iff hcorr ?_ (hkeys (i + k) (l + 1 - k) (by omega) (by omega)
            (by omega))
          intro h
          have := congrArg List.length h
          simp at this
          omega
      refine ⟨?_, ?_⟩
      · intro e he hne B
        simp only [cykTable, List.mem_append, List.mem_map, List.mem_range] at he
        rcases he with he | ⟨i, hi, rfl⟩
        · exact hcorr e he hne B
        · exact hnew i hi B
      · intro j m hm0 hml hjm
        rcases Nat.lt_or_ge m (l + 1) with hlt | hge
        · obtain ⟨e, he, hkey⟩ := hkeys j m hm0 (by omega) hjm
          exact ⟨e, by simp only [cykTable]; exact List.mem_append_left _ he, hkey⟩
        · obtain rfl : m = l + 1 := by omega
          refine ⟨((w.drop j).take (l + 1),
            cykCellFrom g (cykLookup (cykTable g w l)) ((w.drop j).take (l + 1))), ?_, rfl⟩
          simp only [cykTable]
          exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 (by omega), rfl⟩)

variable (g) in
/-- **The CYK recognizer.** The empty word is accepted when there is a production `S → ε`; a
nonempty word when the initial nonterminal is in its cell of the CYK table. -/
def cykAccepts (w : List T) : Bool :=
  if w = [] then decide (∃ r ∈ g.rules, r.input = g.initial ∧ r.output = [])
  else decide (g.initial ∈ cykLookup (cykTable g w w.length) w)

/-- **Correctness of the CYK recognizer** for grammars in Chomsky normal form. -/
theorem cykAccepts_iff (hg : IsChomskyNormalForm g) {w : List T} :
    cykAccepts g w = true ↔ w ∈ g.language := by
  rw [mem_language_iff_yields, cykAccepts]
  split_ifs with hw
  · subst hw
    rw [decide_eq_true_iff]
    constructor
    · rintro ⟨r, hr, hin, hout⟩
      rw [← hin]
      exact yields_of_rule hr (by rw [hout]; exact Yields.nil)
    · intro h
      obtain ⟨B, hB, hrule⟩ := empty_rule_of_yields_nil hg h rfl _ List.mem_cons_self
      obtain rfl := Symbol.nonterminal.inj hB
      exact hrule
  · rw [decide_eq_true_iff]
    obtain ⟨hcorr, hkeys⟩ := cykTable_spec hg w w.length
    have hkey := hkeys 0 w.length (List.length_pos_iff.2 hw) le_rfl (by omega)
    simp only [List.drop_zero, List.take_length] at hkey
    exact mem_cykLookup_iff hcorr hw hkey

end Cslib.Language
