/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Computational infrastructure for Cook–Levin
-/
module

public import Mathlib.Computability.Encoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Basic

/-!
# Computational infrastructure for Cook–Levin

This module provides the CNF encodings and SAT language needed to formulate
Cook–Levin for CNF satisfiability over the repository's canonical complexity
API (`MetaMathlibExt.ComplexityTheory`). NP membership and polynomial-time
reductions are stated through `ComplexityTheory.NP` and
`ComplexityTheory.IsPolyTime`, so the Cook–Levin statement concerns the same
NP class as the P-vs-NP statements. Bitstring framing reuses the canonical
`MetaMathlibExt.BitstringEncoding.delimit`/`undelimit` API.

Primary sources: Stephen A. Cook, "The Complexity of Theorem-Proving
Procedures," *Proceedings of the Third Annual ACM Symposium on Theory of
Computing* (1971), 151–158, <https://doi.org/10.1145/800157.805047>; and
Leonid A. Levin, "Universal Sequential Search Problems," *Problems of
Information Transmission* 9.3 (1973), 265–266.
-/

@[expose] public section

namespace Cslib.CookLevin

/- Compatibility aliases: the CNF representation now lives in
`Cslib.Logic.PL` (`CSLibExt.Logics.Propositional.CNF.Basic`); these keep
the `Cslib.CookLevin` names resolving to the same constants. -/
export Cslib.Logic.PL (CNFClause CNF CNFSat)

/-- Read a unary length prefix, returning the length and the unconsumed suffix. -/
def readUnaryLength : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (readUnaryLength rest).map fun result => (result.1 + 1, result.2)

/-- Prefix-free binary code of a variable index: Mathlib's canonical
natural-number bits wrapped in a canonical self-delimiting block. -/
def encodeNatPrefix (n : Nat) : List Bool :=
  MetaMathlibExt.BitstringEncoding.delimit (Computability.encodeNat n)

/-- Decode a prefix-coded natural and return its unconsumed suffix. -/
def decodeNatPrefix (input : List Bool) : Option (Nat × List Bool) := do
  let (bits, rest) ← MetaMathlibExt.BitstringEncoding.undelimit input
  let n := Computability.decodeNat bits
  if Computability.encodeNat n = bits then some (n, rest) else none

/-- Binary code of a literal: the prefix-free index code followed by its polarity. -/
def encodeLit (l : Nat × Bool) : List Bool :=
  encodeNatPrefix l.1 ++ [l.2]

/-- Decode one literal and return its unconsumed suffix. -/
def decodeLit (input : List Bool) : Option ((Nat × Bool) × List Bool) := do
  let (n, rest) ← decodeNatPrefix input
  match rest with
  | [] => none
  | polarity :: tail => some ((n, polarity), tail)

/-- Decode exactly `n` literals and return the unconsumed suffix. -/
def decodeLits : Nat → List Bool → Option (CNFClause × List Bool)
  | 0, input => some ([], input)
  | n + 1, input => do
      let (literal, rest) ← decodeLit input
      let (literals, tail) ← decodeLits n rest
      some (literal :: literals, tail)

/-- Binary code of a clause: its literal count followed by the encoded literals. -/
def encodeClause (C : CNFClause) : List Bool :=
  List.replicate C.length true ++ false :: C.flatMap encodeLit

/-- Decode one clause and return its unconsumed suffix. -/
def decodeClause (input : List Bool) : Option (CNFClause × List Bool) := do
  let (n, rest) ← readUnaryLength input
  decodeLits n rest

/-- Decode exactly `n` clauses and return the unconsumed suffix. -/
def decodeClauses : Nat → List Bool → Option (CNF × List Bool)
  | 0, input => some ([], input)
  | n + 1, input => do
      let (clause, rest) ← decodeClause input
      let (clauses, tail) ← decodeClauses n rest
      some (clause :: clauses, tail)

/-- Binary code of a CNF formula: its clause count followed by the encoded clauses. -/
def encodeCNF (φ : CNF) : List Bool :=
  List.replicate φ.length true ++ false :: φ.flatMap encodeClause

/-- Decode one CNF formula and return its unconsumed suffix. -/
def decodeCNFAux (input : List Bool) : Option (CNF × List Bool) := do
  let (n, rest) ← readUnaryLength input
  decodeClauses n rest

/-- Decode a complete CNF formula, rejecting missing or trailing bits. -/
def decodeCNF (input : List Bool) : Option CNF := do
  let (φ, rest) ← decodeCNFAux input
  if rest.isEmpty then some φ else none

@[simp] theorem readUnaryLength_replicate (n : Nat) (rest : List Bool) :
    readUnaryLength (List.replicate n true ++ false :: rest) = some (n, rest) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, readUnaryLength, ih]

/-- Soundness of the canonical block parser: a successful parse exhibits
the input as a delimited block followed by the unconsumed suffix. -/
theorem undelimit_eq_some_iff (input bits rest : List Bool) :
    MetaMathlibExt.BitstringEncoding.undelimit input = some (bits, rest) ↔
      input = MetaMathlibExt.BitstringEncoding.delimit bits ++ rest := by
  constructor
  · have aux : ∀ (n : Nat) (input bits rest : List Bool), input.length = n →
        MetaMathlibExt.BitstringEncoding.undelimit input = some (bits, rest) →
        input = MetaMathlibExt.BitstringEncoding.delimit bits ++ rest := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
          intro input bits rest hlen h
          cases input with
          | nil =>
              simp [MetaMathlibExt.BitstringEncoding.undelimit] at h
          | cons bit tail =>
              cases bit with
              | false =>
                  simp only [MetaMathlibExt.BitstringEncoding.undelimit,
                    Option.some.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  simp [MetaMathlibExt.BitstringEncoding.delimit]
              | true =>
                  cases tail with
                  | nil =>
                      simp [MetaMathlibExt.BitstringEncoding.undelimit] at h
                  | cons b tail' =>
                      simp only [MetaMathlibExt.BitstringEncoding.undelimit] at h
                      cases hparse : MetaMathlibExt.BitstringEncoding.undelimit tail' with
                      | none =>
                          simp [hparse] at h
                      | some val =>
                          simp only [hparse, Option.map_some] at h
                          rcases val with ⟨bits', rest'⟩
                          obtain ⟨rfl, rfl⟩ := h
                          have h2 : (true :: b :: tail').length = tail'.length + 2 := rfl
                          have hlt : tail'.length < n := by omega
                          have htail := ih tail'.length hlt tail' _ _ rfl hparse
                          simp [htail, MetaMathlibExt.BitstringEncoding.delimit]
    exact aux input.length input bits rest rfl
  · rintro rfl
    exact MetaMathlibExt.BitstringEncoding.undelimit_delimit bits rest

@[simp] theorem decodeNatPrefix_encodeNatPrefix_append (n : Nat) (rest : List Bool) :
    decodeNatPrefix (encodeNatPrefix n ++ rest) = some (n, rest) := by
  simp [decodeNatPrefix, encodeNatPrefix]

@[simp] theorem decodeLit_encodeLit_append (literal : Nat × Bool) (rest : List Bool) :
    decodeLit (encodeLit literal ++ rest) = some (literal, rest) := by
  rcases literal with ⟨n, polarity⟩
  simp [decodeLit, encodeLit, List.append_assoc]

@[simp] theorem decodeLits_encode_append (literals : CNFClause) (rest : List Bool) :
    decodeLits literals.length (literals.flatMap encodeLit ++ rest) =
      some (literals, rest) := by
  induction literals with
  | nil => simp [decodeLits]
  | cons literal literals ih => simp [decodeLits, List.append_assoc, ih]

@[simp] theorem decodeClause_encodeClause_append (clause : CNFClause) (rest : List Bool) :
    decodeClause (encodeClause clause ++ rest) = some (clause, rest) := by
  simp [decodeClause, encodeClause, List.append_assoc]

@[simp] theorem decodeClauses_encode_append (clauses : CNF) (rest : List Bool) :
    decodeClauses clauses.length (clauses.flatMap encodeClause ++ rest) =
      some (clauses, rest) := by
  induction clauses with
  | nil => simp [decodeClauses]
  | cons clause clauses ih => simp [decodeClauses, List.append_assoc, ih]

@[simp] theorem decodeCNFAux_encodeCNF_append (φ : CNF) (rest : List Bool) :
    decodeCNFAux (encodeCNF φ ++ rest) = some (φ, rest) := by
  simp [decodeCNFAux, encodeCNF, List.append_assoc]

@[simp] theorem decodeCNF_encodeCNF (φ : CNF) : decodeCNF (encodeCNF φ) = some φ := by
  unfold decodeCNF
  rw [show decodeCNFAux (encodeCNF φ) = some (φ, []) by
    simpa using decodeCNFAux_encodeCNF_append φ []]
  rfl

theorem readUnaryLength_eq_some_iff (input : List Bool) (n : Nat) (rest : List Bool) :
    readUnaryLength input = some (n, rest) ↔
      input = List.replicate n true ++ false :: rest := by
  induction input generalizing n rest with
  | nil => simp [readUnaryLength]
  | cons bit input ih =>
      cases bit <;> cases n <;>
        simp [readUnaryLength, ih, List.replicate_succ]

theorem decodeNatPrefix_eq_some_iff (input : List Bool) (n : Nat) (rest : List Bool) :
    decodeNatPrefix input = some (n, rest) ↔ input = encodeNatPrefix n ++ rest := by
  constructor
  · intro h
    unfold decodeNatPrefix at h
    rcases Option.bind_eq_some_iff.mp h with ⟨⟨bits, suffix⟩, hframe, hresult⟩
    dsimp at hresult
    split at hresult
    · rename_i hcanonical
      simp only [Option.some.injEq, Prod.mk.injEq] at hresult
      rcases hresult with ⟨rfl, rfl⟩
      simpa [encodeNatPrefix, hcanonical] using
        (undelimit_eq_some_iff input bits suffix).mp hframe
    · simp at hresult
  · rintro rfl
    exact decodeNatPrefix_encodeNatPrefix_append n rest

theorem decodeLit_eq_some_iff (input : List Bool) (literal : Nat × Bool)
    (rest : List Bool) :
    decodeLit input = some (literal, rest) ↔ input = encodeLit literal ++ rest := by
  rcases literal with ⟨target, targetPolarity⟩
  constructor
  · intro h
    unfold decodeLit at h
    rcases Option.bind_eq_some_iff.mp h with ⟨⟨n, suffix⟩, hnat, hresult⟩
    cases suffix with
    | nil => simp at hresult
    | cons polarity tail =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hresult
        rcases hresult with ⟨⟨rfl, rfl⟩, rfl⟩
        simpa [encodeLit, List.append_assoc] using
          (decodeNatPrefix_eq_some_iff input n (polarity :: tail)).mp hnat
  · rintro rfl
    exact decodeLit_encodeLit_append (target, targetPolarity) rest

theorem decodeLits_eq_some_iff (count : Nat) (input : List Bool)
    (literals : CNFClause) (rest : List Bool) :
    decodeLits count input = some (literals, rest) ↔
      literals.length = count ∧ input = literals.flatMap encodeLit ++ rest := by
  constructor
  · intro h
    induction count generalizing input literals rest with
    | zero =>
        simp only [decodeLits, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp
    | succ count ih =>
        rcases Option.bind_eq_some_iff.mp h with ⟨⟨literal, suffix⟩, hliteral, h⟩
        rcases Option.bind_eq_some_iff.mp h with
          ⟨⟨tailLiterals, tail⟩, htail, hresult⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hresult
        rcases hresult with ⟨rfl, rfl⟩
        rcases ih suffix tailLiterals tail htail with ⟨hlength, hsuffix⟩
        refine ⟨by simp [hlength], ?_⟩
        calc
          input = encodeLit literal ++ suffix :=
            (decodeLit_eq_some_iff input literal suffix).mp hliteral
          _ = encodeLit literal ++ (tailLiterals.flatMap encodeLit ++ tail) := by rw [hsuffix]
          _ = (literal :: tailLiterals).flatMap encodeLit ++ tail := by
            simp [List.append_assoc]
  · rintro ⟨hlength, rfl⟩
    simpa [hlength] using decodeLits_encode_append literals rest

theorem decodeClause_eq_some_iff (input : List Bool) (clause : CNFClause)
    (rest : List Bool) :
    decodeClause input = some (clause, rest) ↔ input = encodeClause clause ++ rest := by
  constructor
  · intro h
    unfold decodeClause at h
    rcases Option.bind_eq_some_iff.mp h with ⟨⟨n, suffix⟩, hread, hdecode⟩
    rcases (decodeLits_eq_some_iff n suffix clause rest).mp hdecode with
      ⟨hlength, hsuffix⟩
    subst n
    calc
      input = List.replicate clause.length true ++ false :: suffix :=
        (readUnaryLength_eq_some_iff input clause.length suffix).mp hread
      _ = encodeClause clause ++ rest := by
        rw [hsuffix]
        simp [encodeClause, List.append_assoc]
  · rintro rfl
    exact decodeClause_encodeClause_append clause rest

theorem decodeClauses_eq_some_iff (count : Nat) (input : List Bool)
    (clauses : CNF) (rest : List Bool) :
    decodeClauses count input = some (clauses, rest) ↔
      clauses.length = count ∧ input = clauses.flatMap encodeClause ++ rest := by
  constructor
  · intro h
    induction count generalizing input clauses rest with
    | zero =>
        simp only [decodeClauses, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp
    | succ count ih =>
        rcases Option.bind_eq_some_iff.mp h with ⟨⟨clause, suffix⟩, hclause, h⟩
        rcases Option.bind_eq_some_iff.mp h with ⟨⟨tailClauses, tail⟩, htail, hresult⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hresult
        rcases hresult with ⟨rfl, rfl⟩
        rcases ih suffix tailClauses tail htail with ⟨hlength, hsuffix⟩
        refine ⟨by simp [hlength], ?_⟩
        calc
          input = encodeClause clause ++ suffix :=
            (decodeClause_eq_some_iff input clause suffix).mp hclause
          _ = encodeClause clause ++ (tailClauses.flatMap encodeClause ++ tail) := by
            rw [hsuffix]
          _ = (clause :: tailClauses).flatMap encodeClause ++ tail := by
            simp [List.append_assoc]
  · rintro ⟨hlength, rfl⟩
    simpa [hlength] using decodeClauses_encode_append clauses rest

theorem decodeCNFAux_eq_some_iff (input : List Bool) (φ : CNF) (rest : List Bool) :
    decodeCNFAux input = some (φ, rest) ↔ input = encodeCNF φ ++ rest := by
  constructor
  · intro h
    unfold decodeCNFAux at h
    rcases Option.bind_eq_some_iff.mp h with ⟨⟨n, suffix⟩, hread, hdecode⟩
    rcases (decodeClauses_eq_some_iff n suffix φ rest).mp hdecode with
      ⟨hlength, hsuffix⟩
    subst n
    calc
      input = List.replicate φ.length true ++ false :: suffix :=
        (readUnaryLength_eq_some_iff input φ.length suffix).mp hread
      _ = encodeCNF φ ++ rest := by
        rw [hsuffix]
        simp [encodeCNF, List.append_assoc]
  · rintro rfl
    exact decodeCNFAux_encodeCNF_append φ rest

/-- A complete CNF decoder succeeds exactly on the canonical encoding of its result. -/
@[simp] theorem decodeCNF_eq_some_iff (input : List Bool) (φ : CNF) :
    decodeCNF input = some φ ↔ input = encodeCNF φ := by
  constructor
  · intro h
    unfold decodeCNF at h
    rcases Option.bind_eq_some_iff.mp h with ⟨⟨parsed, rest⟩, hdecode, hresult⟩
    dsimp at hresult
    split at hresult
    · rename_i hempty
      simp only [Option.some.injEq] at hresult
      subst parsed
      have : rest = [] := by simpa using hempty
      subst rest
      simpa using (decodeCNFAux_eq_some_iff input φ []).mp hdecode
    · simp at hresult
  · rintro rfl
    exact decodeCNF_encodeCNF φ

theorem encodeCNF_injective : Function.Injective encodeCNF := by
  intro φ ψ h
  have := congrArg decodeCNF h
  simpa using this

@[simp] theorem encodeNatPrefix_length (n : Nat) :
    (encodeNatPrefix n).length = 2 * (Computability.encodeNat n).length + 1 := by
  simp [encodeNatPrefix]

@[simp] theorem encodeLit_length (literal : Nat × Bool) :
    (encodeLit literal).length = 2 * (Computability.encodeNat literal.1).length + 2 := by
  simp [encodeLit]

theorem encodeClause_length (clause : CNFClause) :
    (encodeClause clause).length =
      clause.length + 1 + (clause.map fun literal => (encodeLit literal).length).sum := by
  simp [encodeClause, List.length_flatMap]
  omega

theorem encodeCNF_length (φ : CNF) :
    (encodeCNF φ).length =
      φ.length + 1 + (φ.map fun clause => (encodeClause clause).length).sum := by
  simp [encodeCNF, List.length_flatMap]
  omega

/-- A Boolean list encodes a satisfiable CNF formula. -/
def IsSATEncoded (x : List Bool) : Prop :=
  ∃ φ : CNF, encodeCNF φ = x ∧ CNFSat φ

/-- SAT as a language of encoded satisfiable CNF formulas. -/
def SATLang : Set (List Bool) :=
  {x | IsSATEncoded x}

open Classical in
/-- SAT as a decision problem over the canonical complexity API: accept exactly
the bitstrings encoding a satisfiable CNF formula. -/
noncomputable def satDec : MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun x => if x ∈ SATLang then true else false

/-- Polynomial-time many-one reduction between decision problems, expressed
through the canonical `ComplexityTheory.IsPolyTime` predicate. -/
def PolyManyOneRed (L₁ L₂ : MetaMathlibExt.ComplexityTheory.DecisionProblem) : Prop :=
  ∃ reduce : List Bool → List Bool,
    MetaMathlibExt.ComplexityTheory.IsPolyTime reduce ∧ ∀ x, L₁ x = L₂ (reduce x)

end Cslib.CookLevin
