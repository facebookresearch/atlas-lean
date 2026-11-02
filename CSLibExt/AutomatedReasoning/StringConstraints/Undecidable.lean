/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# String constraints with morphisms are undecidable: PCP
-/
module

public import CSLibExt.AutomatedReasoning.StringConstraints.Syntax
public import CSLibExt.Computability.Decidability.PCP
public import CSLibExt.Computability.Decidability.PCPUndecidable
public import Mathlib.Computability.RegularExpressions

/-!
# String constraints with morphisms are undecidable: PCP

The PCP-indexed family of string constraints — word equations,
regular membership, length bounds, and letter-to-word morphisms —
is undecidable: a PCP instance `P` becomes the constraint

* `s ∈ (dominoes of P)⁺`, a regular membership atom, and
* `hom topFun s = hom botFun s`, a word equation between the two
  morphisms that read off the top and bottom words of the dominoes in
  `s`, and
* `|s| ≥ 1`.

A satisfying assignment is exactly a PCP solution: the index word `s`
lists the dominoes, and the equation says their tops and bottoms
concatenate to the same word.

The morphism (transducer) is essential: word equations plus regular
membership alone do not obviously encode PCP, because the block
boundaries of the top and bottom parses of one word need not line up.
With morphisms, the index word itself carries the shared domino
sequence. This is the same boundary that makes the straight-line
fragment (with morphisms) decidable while the general problem is not.

What is *not* proved here: undecidability of the formula-indexed
problem `fun φ : Formula … => ∃ σ, Sat σ φ`. That step would need a
computable encoding `P ↦ pcpConstraint P` and a `Primcodable` /
encoding setup for `Formula`, neither of which is formalized. The
reduction correctness (`pcp_iff_stringSat`) is the mathematical
content; the `TM2Decidable` transfer is stated for the PCP-indexed
family, which is why it needs no `Computable` / `Primcodable`
instance for the constraint syntax.

## Main results

- `pcp_iff_stringSat`: `PCP P` iff the encoding constraint is
  satisfiable.
- `exists_not_tm2Decidable_stringSat`: the PCP-indexed encoding
  family is undecidable, by composing the reduction with CSLibExt's
  undecidability of PCP.

## References

* E. L. Post, *A variant of a recursively unsolvable problem*,
  Bull. AMS 52 (1946), 264–268.
* J. D. Day, V. Ganesh, P. He, F. Manea, D. Nowotka, *The Satisfiability
  of Word Equations: Decidable and Undecidable Theories*, Reachability
  Problems (RP 2018), LNCS 11123, pp. 15–29.
* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed.,
  2013, §5.2 (PCP).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.AutomatedReasoning.StringConstraints

open Cslib.Decidability
open Cslib.Language

variable {α : Type*}

/-- The alphabet for the PCP encoding: dominoes (as index letters) and
plain letters. -/
abbrev BlockSym (α : Type*) := Post.Domino α ⊕ α

/-- A domino as an index letter. -/
abbrev dominoLetter (d : Post.Domino α) : BlockSym α := Sum.inl d

/-- The top morphism: a domino letter maps to its top word as plain
letters; plain letters map to `[]` (they never occur in an index word). -/
def topFun : BlockSym α → List (BlockSym α)
  | Sum.inl d => d.1.map Sum.inr
  | Sum.inr _ => []

/-- The bottom morphism. -/
def botFun : BlockSym α → List (BlockSym α)
  | Sum.inl d => d.2.map Sum.inr
  | Sum.inr _ => []

/-- The regular language of index words: concatenations of domino
letters. -/
def dominoRegex (P : List (Post.Domino α)) : RegularExpression (BlockSym α) :=
  RegularExpression.star ((P.map fun d => RegularExpression.char (Sum.inl d)).sum)

/-- The PCP encoding as a string constraint over one variable. -/
def pcpConstraint (P : List (Post.Domino α)) : Formula (BlockSym α) (Fin 1) :=
  Formula.and
    (Formula.atom (Atom.mem (Term.var 0) (EncodedRegex.flatten (dominoRegex P))))
    (Formula.and
      (Formula.atom (Atom.eq (Term.hom topFun (Term.var 0))
        (Term.hom botFun (Term.var 0))))
      (Formula.atom (Atom.lenGe (Term.var 0) 1)))

/-- The domino named by a one-letter block; junk `([], [])` otherwise. -/
def blockDomino (b : List (BlockSym α)) : Post.Domino α :=
  match b with
  | [Sum.inl d] => d
  | _ => ([], [])

/-- Membership in a sum of regular expressions. -/
theorem mem_sum_matches {rs : List (RegularExpression α)} {w : List α} :
    w ∈ (rs.sum).matches' ↔ ∃ r ∈ rs, w ∈ r.matches' := by
  induction rs with
  | nil => simp [RegularExpression.matches'_zero, Language.notMem_zero]
  | cons r rs ih =>
    rw [List.sum_cons, RegularExpression.matches'_add, Language.mem_add, ih]
    constructor
    · rintro (h | h)
      · exact ⟨r, List.mem_cons_self, h⟩
      · obtain ⟨r', hr', h'⟩ := h
        exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩
    · rintro ⟨r', hr', h'⟩
      rcases List.mem_cons.mp hr' with rfl | hr'
      · exact Or.inl h'
      · exact Or.inr ⟨r', hr', h'⟩

/-- Membership in the index-word language: the word is a concatenation
of domino letters. -/
theorem mem_dominoRegex {P : List (Post.Domino α)} {w : List (BlockSym α)} :
    w ∈ (dominoRegex P).matches' ↔
      ∃ bs : List (List (BlockSym α)), w = bs.flatten ∧
        ∀ b ∈ bs, ∃ d ∈ P, b = [Sum.inl d] := by
  rw [dominoRegex, RegularExpression.matches'_star, Language.mem_kstar]
  constructor
  · rintro ⟨bs, rfl, hbs⟩
    refine ⟨bs, rfl, fun b hb => ?_⟩
    have hb' := hbs b hb
    rw [mem_sum_matches] at hb'
    obtain ⟨r, hr, hbr⟩ := hb'
    rw [List.mem_map] at hr
    obtain ⟨d, hd, hfd⟩ := hr
    refine ⟨d, hd, ?_⟩
    rw [← hfd, RegularExpression.matches'_char] at hbr
    exact Set.mem_singleton_iff.mp hbr
  · rintro ⟨bs, rfl, hbs⟩
    refine ⟨bs, rfl, fun b hb => ?_⟩
    obtain ⟨d, hd, rfl⟩ := hbs b hb
    rw [mem_sum_matches]
    refine ⟨RegularExpression.char (Sum.inl d), ?_, ?_⟩
    · rw [List.mem_map]
      exact ⟨d, hd, rfl⟩
    · rw [RegularExpression.matches'_char]
      exact Set.mem_singleton_iff.mpr rfl

/-- The membership atom of the encoding checks index-word membership. -/
theorem sat_mem_dominoRegex {σ : Fin 1 → List (BlockSym α)}
    {P : List (Post.Domino α)} :
    SatAtom σ (Atom.mem (Term.var 0) (EncodedRegex.flatten (dominoRegex P))) ↔
      σ 0 ∈ (dominoRegex P).matches' := by
  change σ 0 ∈ (EncodedRegex.flatten (dominoRegex P)).toRegex.matches' ↔ _
  rw [EncodedRegex.toRegex_flatten]

/-- The top morphism applied to an index word. -/
theorem flatMap_topFun {w : List (BlockSym α)} {s : List (Post.Domino α)}
    (hw : w = s.map Sum.inl) : w.flatMap topFun = (Post.top s).map Sum.inr := by
  rw [hw, List.flatMap_map]
  simp only [topFun]
  rw [← List.map_flatMap]
  rfl

/-- The bottom morphism applied to an index word. -/
theorem flatMap_botFun {w : List (BlockSym α)} {s : List (Post.Domino α)}
    (hw : w = s.map Sum.inl) : w.flatMap botFun = (Post.bottom s).map Sum.inr := by
  rw [hw, List.flatMap_map]
  simp only [botFun]
  rw [← List.map_flatMap]
  rfl

/-- Flattening a list of one-letter blocks. -/
theorem map_inl_flatten (s : List (Post.Domino α)) :
    s.map dominoLetter = (s.map (fun d => [dominoLetter d])).flatten := by
  induction s with
  | nil => rfl
  | cons d s ih =>
    change dominoLetter d :: s.map dominoLetter
        = [dominoLetter d] ++ (s.map (fun d => [dominoLetter d])).flatten
    rw [ih]
    rfl

/-- **PCP reduces to string-constraint satisfiability.** -/
theorem pcp_iff_stringSat (P : List (Post.Domino α)) :
    Post.PCP P ↔ ∃ σ : Fin 1 → List (BlockSym α), Sat σ (pcpConstraint P) := by
  constructor
  · rintro ⟨s, hsne, hsP, hseq⟩
    refine ⟨fun _ => s.map Sum.inl, ?_⟩
    simp only [pcpConstraint, sat_and, sat_atom]
    refine ⟨?_, ?_, ?_⟩
    · rw [sat_mem_dominoRegex]
      change s.map Sum.inl ∈ (dominoRegex P).matches'
      rw [mem_dominoRegex]
      refine ⟨s.map (fun d => [Sum.inl d]), ?_, fun b hb => ?_⟩
      · exact map_inl_flatten s
      · rw [List.mem_map] at hb
        obtain ⟨d, hd, rfl⟩ := hb
        exact ⟨d, hsP d hd, rfl⟩
    · change eval (fun _ => s.map Sum.inl) (Term.hom topFun (Term.var 0))
          = eval (fun _ => s.map Sum.inl) (Term.hom botFun (Term.var 0))
      simp only [eval_hom, eval_var]
      rw [List.flatMap_map, List.flatMap_map]
      simp only [topFun, botFun]
      rw [← List.map_flatMap, ← List.map_flatMap]
      rw [show s.flatMap (fun d => d.1) = Post.top s from rfl,
        show s.flatMap (fun d => d.2) = Post.bottom s from rfl, hseq]
    · change 1 ≤ (s.map Sum.inl).length
      rw [List.length_map]
      exact Nat.one_le_iff_ne_zero.mpr (fun h => hsne (List.length_eq_zero_iff.mp h))
  · rintro ⟨σ, hSat⟩
    simp only [pcpConstraint, sat_and, sat_atom] at hSat
    obtain ⟨hmem, heq, hlen⟩ := hSat
    rw [sat_mem_dominoRegex] at hmem
    rw [mem_dominoRegex] at hmem
    obtain ⟨bs, hw, hbs⟩ := hmem
    have hblock : ∀ b ∈ bs, b = [Sum.inl (blockDomino b)] := by
      intro b hb
      obtain ⟨d, hd, rfl⟩ := hbs b hb
      rfl
    have hw2 : σ 0 = (bs.map blockDomino).map Sum.inl := by
      rw [hw]
      have haux : ∀ bs : List (List (BlockSym α)),
          (∀ b ∈ bs, b = [Sum.inl (blockDomino b)]) →
            bs.flatten = (bs.map blockDomino).map Sum.inl := by
        intro bs hbs'
        induction bs with
        | nil => rfl
        | cons b bs ih =>
          have hb := hbs' b List.mem_cons_self
          have ih' := ih (fun b' hb' => hbs' b' (List.mem_cons_of_mem _ hb'))
          change b ++ bs.flatten
              = Sum.inl (blockDomino b) :: (bs.map blockDomino).map Sum.inl
          rw [hb, ih']
          rfl
      exact haux bs hblock
    have heq' : (σ 0).flatMap topFun = (σ 0).flatMap botFun := heq
    have htopbot : Post.top (bs.map blockDomino)
        = Post.bottom (bs.map blockDomino) := by
      have h1 := flatMap_topFun hw2
      have h2 := flatMap_botFun hw2
      rw [heq'] at h1
      have hmap : (Post.top (bs.map blockDomino)).map Sum.inr
          = (Post.bottom (bs.map blockDomino)).map Sum.inr := h1.symm.trans h2
      exact (List.map_inj_right Sum.inr_injective).mp hmap
    have hsne : bs.map blockDomino ≠ [] := by
      intro hnil
      have hbsnil : bs = [] := List.map_eq_nil_iff.mp hnil
      have hlen' : 1 ≤ (σ 0).length := hlen
      rw [hw2, List.length_map, List.length_map, hbsnil] at hlen'
      simp at hlen'
    have hsP : ∀ d ∈ bs.map blockDomino, d ∈ P := by
      intro d hd
      rw [List.mem_map] at hd
      obtain ⟨b, hb, hbd⟩ := hd
      obtain ⟨d', hd', hb'⟩ := hbs b hb
      rw [hb'] at hbd
      rw [← hbd]
      exact hd'
    exact ⟨bs.map blockDomino, hsne, hsP, htopbot⟩

/-- **The PCP-indexed encoding family is undecidable** (the
formula-indexed undecidability statement is not formalized; see the
module header). -/
theorem exists_not_tm2Decidable_stringSat :
    ∃ (α : Type) (_ : Fintype α) (_ : Primcodable α),
      ¬ TM2Decidable
        (fun P : List (Post.Domino α) =>
          ∃ σ : Fin 1 → List (BlockSym α), Sat σ (pcpConstraint P)) := by
  obtain ⟨α, hfin, hprim, hund⟩ := exists_not_tm2Decidable_pcp
  refine ⟨α, hfin, hprim, fun h => hund ?_⟩
  obtain ⟨f, hcomp, hiff⟩ := h
  refine ⟨f, hcomp, fun P => ?_⟩
  have hiff' : f (Encodable.encode P) = 1 ↔
      ∃ σ : Fin 1 → List (BlockSym α), Sat σ (pcpConstraint P) := hiff P
  exact hiff'.trans (pcp_iff_stringSat P).symm

end Cslib.AutomatedReasoning.StringConstraints
