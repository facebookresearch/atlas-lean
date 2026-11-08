/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Regularity of context-free languages is undecidable
-/
module

public import CSLibExt.Computability.Decidability.PCPApplications
public import CSLibExt.Computability.Languages.Congruences.Contexts
public import CSLibExt.Computability.Languages.Congruences.Morphisms
public import CSLibExt.Computability.Languages.Finite
public import Cslib.Computability.Languages.MyhillNerode

/-!
# Regularity of context-free languages is undecidable

Whether a context-free grammar generates a regular language is undecidable (`REG_CFG`). The
reduction is from universality (`exists_not_tm2Decidable_univ`). Over the letters of `T`, a
separator `#` and two bits (`Letter T`), a grammar `g` maps to `regGrammar g`, whose language is
(`language_regGrammar`)

  `regLang L(g) = L(g) # {0,1}* ∪ T* # {0ⁿ1ⁿ}`.

* If `L(g)` is every word, this is `T* # {0,1}*`, which is regular (`isRegular_regLang_top`).
* If `u ∉ L(g)`, the words `v` over the bits with `u # v ∈ regLang L(g)` are exactly `0ⁿ1ⁿ`.
  Regular languages are closed under two-sided quotients
  (`Cslib.Language.IsRegular.contextQuotient`) and alphabet preimages
  (`Cslib.Language.IsRegular.alphabetPreimage`), and `{0ⁿ1ⁿ}` is not regular
  (`not_isRegular_zeroOne`, by Myhill–Nerode), so `regLang L(g)` is not regular
  (`not_isRegular_regLang`).

So `g` is universal iff `regGrammar g` generates a regular language (`univ_iff_isRegular`), the map
is primitive recursive (`primrec_regGrammar`), and regularity is undecidable
(`exists_not_tm2Decidable_isRegular`).

## Main results

- `not_isRegular_zeroOne`, `isRegular_regLang_iff`.
- `regGrammar`, `language_regGrammar`, `manyOneReducible_univ_isRegular`,
  `exists_not_tm2Decidable_isRegular`.

## References

* J. E. Hopcroft, R. Motwani, J. D. Ullman, *Introduction to Automata Theory, Languages, and
  Computation*, 3rd ed., Pearson, 2006, §9.5.
* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, Chapter 5
  problems.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability.Regularity

open Cslib.Language

/-! ### The languages -/

section Languages

variable {T : Type}

/-- The letters of the reduction: those of `T`, the separator `#` and two bits. -/
abbrev Letter (T : Type) := Option (T ⊕ Bool)

/-- The separator `#`. -/
def sep : Letter T := none

/-- A letter of `T`. -/
def tl (t : T) : Letter T := some (Sum.inl t)

/-- A bit. -/
def bl (b : Bool) : Letter T := some (Sum.inr b)

/-- The language `{0ⁿ1ⁿ}` over the bits (`false` for `0`). -/
def zeroOne : Language Bool := {w | ∃ n, w = List.replicate n false ++ List.replicate n true}

/-- The target language `L # {0,1}* ∪ T* # {0ⁿ1ⁿ}`. -/
def regLang (L : Language T) : Language (Letter T) :=
  {w | ∃ (u : List T) (v : List Bool), w = u.map tl ++ sep :: v.map bl ∧ (u ∈ L ∨ v ∈ zeroOne)}

theorem bl_injective : Function.Injective (bl (T := T)) := fun a b h ↦ by
  simpa [bl] using h

/-- A word `u # v` determines `u` and `v`. -/
theorem eq_of_map_tl_append_sep :
    ∀ {u u' : List T} {v v' : List Bool},
      u.map tl ++ sep :: v.map bl = u'.map tl ++ sep :: v'.map bl → u = u' ∧ v = v'
  | [], [], v, v', h => by
    simp only [List.map_nil, List.nil_append, List.cons.injEq, true_and] at h
    exact ⟨rfl, (List.map_injective_iff.mpr bl_injective) h⟩
  | [], _ :: _, _, _, h => by simp [sep, tl] at h
  | _ :: _, [], _, _, h => by simp [sep, tl] at h
  | a :: u, a' :: u', v, v', h => by
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := eq_of_map_tl_append_sep h.2
    exact ⟨by simpa [tl] using h.1, rfl⟩

/-- **`{0ⁿ1ⁿ}` is not regular**: the words `0ⁱ` are pairwise inequivalent for the Nerode
congruence. -/
theorem not_isRegular_zeroOne : ¬zeroOne.IsRegular := by
  intro h
  have hfin := Language.IsRegular.iff_finite_nerodeQuotient.mp h
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ ↦ (Quotient.mk _ (List.replicate n false) : zeroOne.NerodeQuotient))
  have hr := (Quotient.exact heq) (List.replicate i true)
  have hmem : List.replicate j false ++ List.replicate i true ∈ zeroOne :=
    hr.mp ⟨i, rfl⟩
  obtain ⟨n, hn⟩ := hmem
  have h₁ := congrArg (List.count false) hn
  have h₂ := congrArg (List.count true) hn
  simp [List.count_replicate] at h₁ h₂
  omega

/-- The words over the letters of `T`. -/
def letterWords : Language (Letter T) := {w | ∃ u : List T, w = u.map tl}

/-- The words over the bits. -/
def bitWords : Language (Letter T) := {w | ∃ v : List Bool, w = v.map bl}

/-- The one-letter words over the letters of `T`. -/
def letterSet : Language (Letter T) := {w | ∃ t : T, w = [tl t]}

/-- The one-letter words over the bits. -/
def bitSet : Language (Letter T) := {w | ∃ b : Bool, w = [bl b]}

theorem letterWords_eq : (letterWords : Language (Letter T)) = KStar.kstar letterSet := by
  ext w
  rw [Language.mem_kstar]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨u.map fun t ↦ [tl t], ?_, fun y hy ↦ ?_⟩
    · induction u with
      | nil => rfl
      | cons a u ih => simp [ih]
    · obtain ⟨t, -, rfl⟩ := List.mem_map.mp hy
      exact ⟨t, rfl⟩
  · rintro ⟨L, rfl, hL⟩
    induction L with
    | nil => exact ⟨[], rfl⟩
    | cons y L ih =>
      obtain ⟨t, rfl⟩ := hL y (List.mem_cons_self ..)
      obtain ⟨u, hu⟩ := ih fun z hz ↦ hL z (List.mem_cons_of_mem _ hz)
      exact ⟨t :: u, by simp [hu]⟩

theorem bitWords_eq : (bitWords : Language (Letter T)) = KStar.kstar bitSet := by
  ext w
  rw [Language.mem_kstar]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨v.map fun b ↦ [bl b], ?_, fun y hy ↦ ?_⟩
    · induction v with
      | nil => rfl
      | cons a v ih => simp [ih]
    · obtain ⟨b, -, rfl⟩ := List.mem_map.mp hy
      exact ⟨b, rfl⟩
  · rintro ⟨L, rfl, hL⟩
    induction L with
    | nil => exact ⟨[], rfl⟩
    | cons y L ih =>
      obtain ⟨b, rfl⟩ := hL y (List.mem_cons_self ..)
      obtain ⟨v, hv⟩ := ih fun z hz ↦ hL z (List.mem_cons_of_mem _ hz)
      exact ⟨b :: v, by simp [hv]⟩

theorem isRegular_letterWords [Finite T] : (letterWords : Language (Letter T)).IsRegular := by
  have hfin : Set.Finite (letterSet : Language (Letter T)) := by
    simpa [letterSet, Set.range, eq_comm] using Set.finite_range fun t : T ↦ [tl t]
  rw [letterWords_eq]
  exact Cslib.Language.IsRegular.kstar (IsRegular.of_finite hfin)

theorem isRegular_bitWords : (bitWords : Language (Letter T)).IsRegular := by
  have hfin : Set.Finite (bitSet : Language (Letter T)) := by
    simpa [bitSet, Set.range, eq_comm] using Set.finite_range fun b : Bool ↦ [(bl b : Letter T)]
  rw [bitWords_eq]
  exact Cslib.Language.IsRegular.kstar (IsRegular.of_finite hfin)

/-- **If `L` is every word, `regLang L = T* # {0,1}*` is regular.** -/
theorem isRegular_regLang_top [Finite T] {L : Language T} (hL : ∀ u, u ∈ L) :
    (regLang L).IsRegular := by
  have heq : regLang L = letterWords * ({[sep]} : Language (Letter T)) * bitWords := by
    ext w
    constructor
    · rintro ⟨u, v, rfl, -⟩
      exact Language.mem_mul.mpr ⟨u.map tl ++ [sep],
        Language.mem_mul.mpr ⟨u.map tl, ⟨u, rfl⟩, [sep], rfl, rfl⟩, v.map bl, ⟨v, rfl⟩, by simp⟩
    · intro hw
      obtain ⟨x, hx, _, ⟨v, rfl⟩, rfl⟩ := Language.mem_mul.mp hw
      obtain ⟨_, ⟨u, rfl⟩, y, hy, rfl⟩ := Language.mem_mul.mp hx
      rw [Set.mem_singleton_iff.mp hy]
      exact ⟨u, v, by simp, Or.inl (hL u)⟩
  rw [heq]
  exact Cslib.Language.IsRegular.mul
    (Cslib.Language.IsRegular.mul isRegular_letterWords (Cslib.Language.IsRegular.char sep))
    isRegular_bitWords

/-- **If `u ∉ L`, `regLang L` is not regular**: its quotient by `u #`, read over the bits, is
`{0ⁿ1ⁿ}`. -/
theorem not_isRegular_regLang {L : Language T} {u : List T} (hu : u ∉ L) :
    ¬(regLang L).IsRegular := by
  intro h
  have heq : alphabetPreimage bl (contextQuotient (regLang L) (u.map tl ++ [sep]) []) =
      zeroOne := by
    ext v
    simp only [alphabetPreimage, contextQuotient, regLang, List.append_nil]
    constructor
    · rintro ⟨u', v', h', hor⟩
      obtain ⟨rfl, rfl⟩ := eq_of_map_tl_append_sep (by simpa using h')
      exact hor.resolve_left hu
    · intro hv
      exact ⟨u, v, by simp, Or.inr hv⟩
  exact not_isRegular_zeroOne (heq ▸ Cslib.Language.IsRegular.alphabetPreimage
    (Cslib.Language.IsRegular.contextQuotient h (u.map tl ++ [sep]) []) bl)

/-- `regLang L` is regular iff `L` is every word. -/
theorem isRegular_regLang_iff [Finite T] {L : Language T} :
    (regLang L).IsRegular ↔ ∀ u, u ∈ L := by
  refine ⟨fun h ↦ ?_, isRegular_regLang_top⟩
  by_contra hne
  push Not at hne
  obtain ⟨u, hu⟩ := hne
  exact not_isRegular_regLang hu h

end Languages

/-! ### The grammar -/

section Grammar

variable {T : Type} [Fintype T] [DecidableEq T]

/-- A symbol of `g`, in `regGrammar g`: nonterminals are shifted by `4`, letters map by `tl`. -/
def shiftSym : ℕ ⊕ T → ℕ ⊕ Letter T :=
  Sum.map (· + 4) tl

/-- A production of `g`, in `regGrammar g`. -/
def shiftRule (e : ℕ × List (ℕ ⊕ T)) : ℕ × List (ℕ ⊕ Letter T) :=
  (e.1 + 4, e.2.map shiftSym)

/-- The productions of `regGrammar g` besides those of `g`, with `s` the start of `g`:
`0 → (s+4) # 1 | 2 # 3`, `1 → ε | 0 1 | 1 1` (bits), `2 → ε | a 2` (letters of `T`) and
`3 → ε | 0 3 1` (`0ⁿ1ⁿ`). -/
noncomputable def fixedRules (s : ℕ) : List (ℕ × List (ℕ ⊕ Letter T)) :=
  [(0, [Sum.inl (s + 4), Sum.inr sep, Sum.inl 1]), (0, [Sum.inl 2, Sum.inr sep, Sum.inl 3]),
    (1, []), (1, [Sum.inr (bl false), Sum.inl 1]), (1, [Sum.inr (bl true), Sum.inl 1]),
    (2, []), (3, []), (3, [Sum.inr (bl false), Sum.inl 3, Sum.inr (bl true)])] ++
  (Finset.univ : Finset T).toList.map fun t ↦ (2, [Sum.inr (tl t), Sum.inl 2])

/-- The grammar of `regLang L(g)`. -/
noncomputable def regGrammar (g : EncodedCFG T) : EncodedCFG (Letter T) :=
  ⟨0, fixedRules g.start ++ g.rules.map shiftRule⟩

/-- The languages of the nonterminals of `regGrammar g`. -/
def regVal (g : EncodedCFG T) : ℕ → Language (Letter T)
  | 0 => regLang g.language
  | 1 => bitWords
  | 2 => letterWords
  | 3 => {w | ∃ v ∈ zeroOne, w = v.map bl}
  | n + 4 => {w | ∃ u ∈ languageFrom g.toCFG n, w = u.map tl}

omit [Fintype T] in
/-- The interpretation of a shifted right-hand side is the image of the original one. -/
theorem mem_evalForm_shift {g : EncodedCFG T} {w : List (Letter T)} :
    ∀ {out : List (ℕ ⊕ T)},
      w ∈ evalForm (regVal g) ((out.map shiftSym).map EncodedCFG.decodeSymbol) →
        ∃ u ∈ evalForm (languageFrom g.toCFG) (out.map EncodedCFG.decodeSymbol), w = u.map tl
  | [], hw => ⟨[], Language.nil_mem_one, by simpa using (Language.mem_one w).mp hw⟩
  | x :: out, hw => by
    simp only [List.map_cons, evalForm_cons] at hw ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := Language.mem_mul.mp hw
    obtain ⟨u, hu, rfl⟩ := mem_evalForm_shift hb
    cases x with
    | inl n =>
      obtain ⟨u₀, hu₀, rfl⟩ := ha
      exact ⟨u₀ ++ u, Language.mem_mul.mpr ⟨u₀, hu₀, u, hu, rfl⟩, by simp⟩
    | inr t =>
      have ha' : a = [tl t] := ha
      subst ha'
      exact ⟨t :: u, Language.mem_mul.mpr ⟨[t], rfl, u, hu, rfl⟩, by simp⟩

/-- **Every production of `regGrammar g` is sound for `regVal g`.** -/
theorem isValuation_regVal (g : EncodedCFG T) : IsValuation (regGrammar g).toCFG (regVal g) := by
  intro r hr
  obtain ⟨e, he, rfl⟩ := EncodedCFG.mem_toCFG_rules.mp hr
  simp only [regGrammar, fixedRules, List.mem_append, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at he
  rcases he with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨t, -, rfl⟩) | ⟨e₀, he₀, rfl⟩
  · -- `0 → (s+4) # 1`
    intro w hw
    simp only [EncodedCFG.decodeRule, List.map_cons, List.map_nil, evalForm_cons,
      evalForm_nil] at hw
    obtain ⟨a, ⟨u, hu, rfl⟩, b, hb, rfl⟩ := Language.mem_mul.mp hw
    obtain ⟨c, hc, d, hd, rfl⟩ := Language.mem_mul.mp hb
    obtain ⟨_, ⟨v, rfl⟩, _, rfl, rfl⟩ := Language.mem_mul.mp hd
    rw [Set.mem_singleton_iff.mp hc]
    exact ⟨u, v, by simp, Or.inl hu⟩
  · -- `0 → 2 # 3`
    intro w hw
    simp only [EncodedCFG.decodeRule, List.map_cons, List.map_nil, evalForm_cons,
      evalForm_nil] at hw
    obtain ⟨a, ⟨u, rfl⟩, b, hb, rfl⟩ := Language.mem_mul.mp hw
    obtain ⟨c, hc, d, hd, rfl⟩ := Language.mem_mul.mp hb
    obtain ⟨_, ⟨v, hv, rfl⟩, _, rfl, rfl⟩ := Language.mem_mul.mp hd
    rw [Set.mem_singleton_iff.mp hc]
    exact ⟨u, v, by simp, Or.inr hv⟩
  · intro w hw
    exact ⟨[], by simpa using (Language.mem_one w).mp hw⟩
  · intro w hw
    simp only [EncodedCFG.decodeRule, List.map_cons, List.map_nil, evalForm_cons,
      evalForm_nil] at hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Language.mem_mul.mp hw
    obtain ⟨_, ⟨v, rfl⟩, _, rfl, rfl⟩ := Language.mem_mul.mp hb
    rw [Set.mem_singleton_iff.mp ha]
    exact ⟨false :: v, by simp⟩
  · intro w hw
    simp only [EncodedCFG.decodeRule, List.map_cons, List.map_nil, evalForm_cons,
      evalForm_nil] at hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Language.mem_mul.mp hw
    obtain ⟨_, ⟨v, rfl⟩, _, rfl, rfl⟩ := Language.mem_mul.mp hb
    rw [Set.mem_singleton_iff.mp ha]
    exact ⟨true :: v, by simp⟩
  · intro w hw
    exact ⟨[], by simpa using (Language.mem_one w).mp hw⟩
  · intro w hw
    exact ⟨[], ⟨0, rfl⟩, by simpa using (Language.mem_one w).mp hw⟩
  · -- `3 → 0 3 1`
    intro w hw
    simp only [EncodedCFG.decodeRule, List.map_cons, List.map_nil, evalForm_cons,
      evalForm_nil] at hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Language.mem_mul.mp hw
    obtain ⟨_, ⟨v, ⟨n, rfl⟩, rfl⟩, d, hd, rfl⟩ := Language.mem_mul.mp hb
    obtain ⟨c, hc, _, rfl, rfl⟩ := Language.mem_mul.mp hd
    rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hc]
    refine ⟨List.replicate (n + 1) false ++ List.replicate (n + 1) true, ⟨n + 1, rfl⟩, ?_⟩
    simp only [List.replicate_succ, List.cons_append, List.map_cons, List.map_append,
      List.append_assoc, List.append_nil, List.map_replicate]
    rw [← List.replicate_succ', List.replicate_succ]
    simp
  · -- `2 → a 2`
    intro w hw
    simp only [EncodedCFG.decodeRule, List.map_cons, List.map_nil, evalForm_cons,
      evalForm_nil] at hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Language.mem_mul.mp hw
    obtain ⟨_, ⟨u, rfl⟩, _, rfl, rfl⟩ := Language.mem_mul.mp hb
    rw [Set.mem_singleton_iff.mp ha]
    exact ⟨t :: u, by simp⟩
  · -- a shifted production of `g`
    intro w hw
    obtain ⟨u, hu, rfl⟩ := mem_evalForm_shift (g := g) (out := e₀.2) hw
    exact ⟨u, isValuation_languageFrom _ (EncodedCFG.mem_toCFG_rules.mpr ⟨e₀, he₀, rfl⟩) hu,
      rfl⟩

/-! ### Completeness: the words of `regLang L(g)` are generated -/

theorem mem_languageFrom_of_mem_rules {g : EncodedCFG T} {e : ℕ × List (ℕ ⊕ Letter T)}
    (he : e ∈ (regGrammar g).rules) {w : List (Letter T)}
    (hw : w ∈ evalForm (languageFrom (regGrammar g).toCFG) (EncodedCFG.decodeRule e).output) :
    w ∈ languageFrom (regGrammar g).toCFG e.1 :=
  isValuation_languageFrom _ (EncodedCFG.mem_toCFG_rules.mpr ⟨e, he, rfl⟩) hw

theorem bits_mem (g : EncodedCFG T) (v : List Bool) :
    v.map bl ∈ languageFrom (regGrammar g).toCFG 1 := by
  induction v with
  | nil =>
    exact mem_languageFrom_of_mem_rules (e := (1, [])) (by simp [regGrammar, fixedRules])
      (Language.nil_mem_one)
  | cons b v ih =>
    refine mem_languageFrom_of_mem_rules (e := (1, [Sum.inr (bl b), Sum.inl 1]))
      (by cases b <;> simp [regGrammar, fixedRules]) ?_
    exact Language.mem_mul.mpr ⟨[bl b], rfl, v.map bl,
      Language.mem_mul.mpr ⟨_, ih, [], Language.nil_mem_one, by simp⟩, rfl⟩

theorem letters_mem (g : EncodedCFG T) (u : List T) :
    u.map tl ∈ languageFrom (regGrammar g).toCFG 2 := by
  induction u with
  | nil =>
    exact mem_languageFrom_of_mem_rules (e := (2, [])) (by simp [regGrammar, fixedRules])
      (Language.nil_mem_one)
  | cons t u ih =>
    refine mem_languageFrom_of_mem_rules (e := (2, [Sum.inr (tl t), Sum.inl 2]))
      (by simp [regGrammar, fixedRules]) ?_
    exact Language.mem_mul.mpr ⟨[tl t], rfl, u.map tl,
      Language.mem_mul.mpr ⟨_, ih, [], Language.nil_mem_one, by simp⟩, rfl⟩

theorem zeroOne_mem (g : EncodedCFG T) (n : ℕ) :
    (List.replicate n false ++ List.replicate n true).map bl ∈
      languageFrom (regGrammar g).toCFG 3 := by
  induction n with
  | zero =>
    exact mem_languageFrom_of_mem_rules (e := (3, [])) (by simp [regGrammar, fixedRules])
      (Language.nil_mem_one)
  | succ n ih =>
    refine mem_languageFrom_of_mem_rules
      (e := (3, [Sum.inr (bl false), Sum.inl 3, Sum.inr (bl true)]))
      (by simp [regGrammar, fixedRules]) ?_
    refine Language.mem_mul.mpr ⟨[bl false], rfl, _, Language.mem_mul.mpr ⟨_, ih, [bl true],
      Language.mem_mul.mpr ⟨[bl true], rfl, [], Language.nil_mem_one, rfl⟩, rfl⟩, ?_⟩
    simp only [List.replicate_succ, List.cons_append, List.map_cons, List.map_append,
      List.map_replicate, List.append_assoc]
    rw [← List.replicate_succ', List.replicate_succ]
    simp

/-- A shifted right-hand side generates the images of the original words. -/
theorem mem_evalForm_shift_of {g : EncodedCFG T} {W : ℕ → Language T}
    (hW : ∀ n u, u ∈ W n → u.map tl ∈ languageFrom (regGrammar g).toCFG (n + 4)) :
    ∀ {out : List (ℕ ⊕ T)} {u : List T}, u ∈ evalForm W (out.map EncodedCFG.decodeSymbol) →
      u.map tl ∈ evalForm (languageFrom (regGrammar g).toCFG)
        ((out.map shiftSym).map EncodedCFG.decodeSymbol)
  | [], u, hu => by simpa using hu
  | x :: out, u, hu => by
    simp only [List.map_cons, evalForm_cons] at hu ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := Language.mem_mul.mp hu
    refine Language.mem_mul.mpr ⟨a.map tl, ?_, b.map tl, mem_evalForm_shift_of hW hb, by simp⟩
    cases x with
    | inl n => exact hW n a ha
    | inr t =>
      have ha' : a = [t] := ha
      subst ha'
      rfl

/-- The images of the words of `g` from `n` are generated from `n + 4`. -/
theorem shift_mem (g : EncodedCFG T) {n : ℕ} {u : List T} (hu : u ∈ languageFrom g.toCFG n) :
    u.map tl ∈ languageFrom (regGrammar g).toCFG (n + 4) := by
  let W : ℕ → Language T := fun n ↦ {u | u.map tl ∈ languageFrom (regGrammar g).toCFG (n + 4)}
  have hW : IsValuation g.toCFG W := by
    intro r hr
    obtain ⟨e₀, he₀, rfl⟩ := EncodedCFG.mem_toCFG_rules.mp hr
    intro u hu
    exact mem_languageFrom_of_mem_rules (e := shiftRule e₀)
      (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨e₀, he₀, rfl⟩)))
      (mem_evalForm_shift_of (fun _ _ h ↦ h) hu)
  have hle := evalForm_le_of_derives hW (mem_languageFrom.mp hu)
  have hmem : u ∈ evalForm W (u.map Symbol.terminal) := by
    rw [evalForm_map_terminal]
    rfl
  have := hle hmem
  simp only [evalForm_cons, evalForm_nil, evalSymbol_nonterminal, mul_one] at this
  exact this

/-- **The language of `regGrammar g` is `regLang L(g)`.** -/
theorem language_regGrammar (g : EncodedCFG T) : (regGrammar g).language = regLang g.language := by
  refine le_antisymm (language_le_of_valuation (isValuation_regVal g)) ?_
  rintro _ ⟨u, v, rfl, hu | hv⟩
  · refine mem_languageFrom_of_mem_rules
      (e := (0, [Sum.inl (g.start + 4), Sum.inr sep, Sum.inl 1])) (by simp [regGrammar, fixedRules])
      (Language.mem_mul.mpr ⟨u.map tl, shift_mem g hu, _, Language.mem_mul.mpr ⟨[sep], rfl, _,
        Language.mem_mul.mpr ⟨_, bits_mem g v, [], Language.nil_mem_one, rfl⟩, rfl⟩, ?_⟩)
    simp
  · obtain ⟨n, rfl⟩ := hv
    refine mem_languageFrom_of_mem_rules
      (e := (0, [Sum.inl 2, Sum.inr sep, Sum.inl 3])) (by simp [regGrammar, fixedRules])
      (Language.mem_mul.mpr ⟨u.map tl, letters_mem g u, _, Language.mem_mul.mpr ⟨[sep], rfl, _,
        Language.mem_mul.mpr ⟨_, zeroOne_mem g n, [], Language.nil_mem_one, rfl⟩, rfl⟩, ?_⟩)
    simp

/-! ### The reduction -/

/-- **A grammar generates every word iff `regGrammar g` generates a regular language.** -/
theorem univ_iff_isRegular (g : EncodedCFG T) :
    (∀ w, w ∈ g.language) ↔ (regGrammar g).language.IsRegular := by
  rw [language_regGrammar, isRegular_regLang_iff]

variable [Primcodable T]

omit [Fintype T] [DecidableEq T] in
theorem primrec_shiftSym : Primrec (shiftSym (T := T)) :=
  (Primrec.sumCasesOn Primrec.id
    (Primrec.sumInl.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const 4))).to₂
    (Primrec.sumInr.comp (Primrec.option_some.comp (Primrec.sumInl.comp Primrec.snd))).to₂).of_eq
    fun x ↦ by cases x <;> rfl

omit [Fintype T] [DecidableEq T] in
theorem primrec_shiftRule : Primrec (shiftRule (T := T)) :=
  Primrec.pair (Primrec.nat_add.comp Primrec.fst (Primrec.const 4))
    (Primrec.list_map Primrec.snd (primrec_shiftSym.comp Primrec.snd).to₂)

omit [DecidableEq T] in
theorem primrec_fixedRules : Primrec (fixedRules (T := T)) :=
  (Primrec.list_cons.comp (Primrec.pair (Primrec.const 0) (Primrec.list_cons.comp
    (Primrec.sumInl.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 4)))
    (Primrec.const _))) (Primrec.const _)).of_eq fun _ ↦ rfl

omit [DecidableEq T] in
theorem primrec_regGrammar : Primrec (regGrammar (T := T)) :=
  (EncodedCFG.primrec₂_mk.comp (Primrec.const 0) (Primrec.list_append.comp
    (primrec_fixedRules.comp EncodedCFG.primrec_start)
    (Primrec.list_map EncodedCFG.primrec_rules (primrec_shiftRule.comp Primrec.snd).to₂))).of_eq
    fun _ ↦ rfl

/-- **Universality many-one reduces to regularity of context-free languages.** -/
theorem manyOneReducible_univ_isRegular :
    ManyOneReducible (fun g : EncodedCFG T ↦ ∀ w, w ∈ g.language)
      (fun g : EncodedCFG (Letter T) ↦ g.language.IsRegular) :=
  ⟨regGrammar, primrec_regGrammar.to_comp, univ_iff_isRegular⟩

end Grammar

end Cslib.Decidability.Regularity

namespace Cslib.Decidability

open Cslib.Language Regularity

/-- **Regularity of context-free languages is undecidable** (`REG_CFG`), over a finite
alphabet. -/
theorem exists_not_tm2Decidable_isRegular :
    ∃ (T : Type) (_ : Fintype T) (_ : Primcodable T) (_ : DecidableEq T),
      ¬TM2Decidable fun g : EncodedCFG T ↦ g.language.IsRegular := by
  obtain ⟨T, _, _, _, h⟩ := exists_not_tm2Decidable_univ
  exact ⟨Letter T, inferInstance, inferInstance, inferInstance, fun hd ↦
    h (tm2Decidable_of_manyOneReducible manyOneReducible_univ_isRegular hd)⟩

end Cslib.Decidability
