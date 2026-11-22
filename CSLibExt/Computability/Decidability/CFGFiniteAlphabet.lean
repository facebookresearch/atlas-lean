/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.TerminalCoding
public import CSLibExt.Computability.Decidability.PCPBinary
public import CSLibExt.Computability.Decidability.PCPAmbiguity

/-!
# Undecidability of overlap and ambiguity for binary context-free grammars

The existing PCP reductions produce grammars over `Bool ⊕ ℕ`: index markers are terminals,
so that alphabet is infinite. We encode it globally by `false ↦ 0`, `true ↦ 1`, `inr n ↦ n+2`,
then use the existing unary binary code `i ↦ 1ⁱ0`. The conversion of grammar encodings is
primitive recursive on the entire infinite source alphabet, not merely on the finite set
of symbols appearing in one grammar.

Composing the existing PCP reductions with terminal coding gives genuine many-one
reductions to overlap and to leftmost-rule-trace ambiguity of `EncodedCFG Bool`. Unary
coding makes no claim about polynomial running time or description size.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability.Post

/-- The existing unary code is primitive recursive whenever its indexing is, including
indexings of infinite alphabets. -/
theorem primrec_unaryCode {α : Type*} [Primcodable α] {e : α → ℕ} (he : Primrec e) :
    Primrec (unaryCode e) := by
  have hrep : Primrec fun a => (List.range (e a)).map (fun _ : ℕ => true) :=
    Primrec.list_map (Primrec.list_range.comp he) (Primrec.const true).to₂
  exact (Primrec.list_append.comp hrep (Primrec.const [false])).of_eq fun a => by
    simp [unaryCode, List.map_const']

end Cslib.Decidability.Post

namespace Cslib.Decidability.Grammar

open Cslib.Language Post

/-- A global numbering of PCP's two letter terminals and all natural-number index terminals. -/
def boolNatIndex : Bool ⊕ ℕ → ℕ
  | .inl false => 0
  | .inl true => 1
  | .inr n => n + 2

/-- All source terminals, including arbitrarily large index markers, have distinct numbers. -/
theorem boolNatIndex_injective : Function.Injective boolNatIndex := by
  rintro (a | m) (b | n) h
  · cases a <;> cases b <;> simp_all [boolNatIndex]
  · cases a <;> simp only [boolNatIndex] at h <;> omega
  · cases b <;> simp only [boolNatIndex] at h <;> omega
  · simp only [boolNatIndex, Nat.add_right_cancel_iff] at h
    exact congrArg Sum.inr h

/-- Primitive recursiveness is proved by Sum elimination and natural-number addition.
The finite-domain fact applies only to the Bool branch, never to `Bool ⊕ ℕ`. -/
theorem primrec_boolNatIndex : Primrec boolNatIndex := by
  have hb : Primrec Bool.toNat := Primrec.dom_finite _
  exact (Primrec.sumCasesOn Primrec.id (hb.comp Primrec.snd).to₂
    (Primrec.nat_add.comp Primrec.snd (Primrec.const 2)).to₂).of_eq fun s => by
      cases s with
      | inl b => cases b <;> rfl
      | inr n => rfl

/-- The induced binary word homomorphism is injective on the infinite source alphabet. -/
theorem boolNatWord_injective :
    Function.Injective (_root_.Language.Hom.lift (unaryCode boolNatIndex)) :=
  unaryHom_injective boolNatIndex_injective

/-- Convert an encoded grammar over `Bool ⊕ ℕ` to a grammar with the fixed alphabet `Bool`. -/
def binaryCFG : EncodedCFG (Bool ⊕ ℕ) → EncodedCFG Bool :=
  EncodedCFG.mapTerminals (unaryCode boolNatIndex)

/-- The actual conversion of encoded grammars is primitive recursive. -/
theorem primrec_binaryCFG : Primrec binaryCFG :=
  EncodedCFG.primrec_mapTerminals (primrec_unaryCode primrec_boolNatIndex)

/-- Binary conversion has exactly the canonical homomorphic-image language. -/
theorem language_binaryCFG (g : EncodedCFG (Bool ⊕ ℕ)) :
    (binaryCFG g).language =
      g.language.image (_root_.Language.Hom.lift (unaryCode boolNatIndex)) :=
  EncodedCFG.language_mapTerminals _ _

/-- The binary conversions overlap exactly when the source grammars overlap. -/
theorem overlap_binaryCFG_iff (g₁ g₂ : EncodedCFG (Bool ⊕ ℕ)) :
    (∃ w, w ∈ (binaryCFG g₁).language ∧ w ∈ (binaryCFG g₂).language) ↔
      ∃ w, w ∈ g₁.language ∧ w ∈ g₂.language :=
  EncodedCFG.overlap_mapTerminals_iff _ boolNatWord_injective _ _

/-- Binary conversion preserves and reflects ambiguity of the grammar's exact leftmost traces. -/
theorem isAmbiguous_binaryCFG_iff (g : EncodedCFG (Bool ⊕ ℕ)) :
    IsAmbiguous (binaryCFG g).toCFG ↔ IsAmbiguous g.toCFG :=
  EncodedCFG.isAmbiguous_mapTerminals_iff boolNatWord_injective

/-- PCP over Bool many-one reduces to overlap of grammars over the fixed binary alphabet. -/
theorem manyOneReducible_pcp_overlap_bool :
    ManyOneReducible (PCP (α := Bool)) fun g : EncodedCFG Bool × EncodedCFG Bool =>
      ∃ w, w ∈ g.1.language ∧ w ∈ g.2.language := by
  refine (manyOneReducible_pcp_inter (α := Bool)).trans ?_
  exact ⟨fun g => (binaryCFG g.1, binaryCFG g.2),
    (Primrec.pair (primrec_binaryCFG.comp Primrec.fst)
      (primrec_binaryCFG.comp Primrec.snd)).to_comp,
    fun g => (overlap_binaryCFG_iff g.1 g.2).symm⟩

/-- PCP over Bool many-one reduces to ambiguity of grammars over the fixed binary alphabet. -/
theorem manyOneReducible_pcp_isAmbiguous_bool :
    ManyOneReducible (PCP (α := Bool)) fun g : EncodedCFG Bool => IsAmbiguous g.toCFG := by
  refine (manyOneReducible_pcp_isAmbiguous (α := Bool)).trans ?_
  exact ⟨binaryCFG, primrec_binaryCFG.to_comp, fun g => (isAmbiguous_binaryCFG_iff g).symm⟩

end Cslib.Decidability.Grammar

namespace Cslib.Decidability

open Cslib.Language Grammar

/-- Overlap of context-free grammars is undecidable even with the fixed alphabet Bool. -/
theorem not_tm2Decidable_overlap_bool :
    ¬TM2Decidable fun g : EncodedCFG Bool × EncodedCFG Bool =>
      ∃ w, w ∈ g.1.language ∧ w ∈ g.2.language :=
  fun h => not_tm2Decidable_pcp_bool
    (tm2Decidable_of_manyOneReducible manyOneReducible_pcp_overlap_bool h)

/-- Ambiguity of context-free grammars is undecidable even with the fixed alphabet Bool. -/
theorem not_tm2Decidable_isAmbiguous_bool :
    ¬TM2Decidable fun g : EncodedCFG Bool => IsAmbiguous g.toCFG :=
  fun h => not_tm2Decidable_pcp_bool
    (tm2Decidable_of_manyOneReducible manyOneReducible_pcp_isAmbiguous_bool h)

end Cslib.Decidability
