/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal word and prior-reference bounds for finite contextual equation certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationFiniteEquationSources

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every packed signed letter must name an actual letter of the finite alphabet. -/
def y322RawEquationWordAllowed (alphabet : ℕ) (word : List ℕ) : Prop :=
  ∀ packed ∈ word, packed / 2 < alphabet

/-- Decode exactly the signed letters whose literal finite alphabet bounds were checked. -/
def y322RawEquationWordDecode (alphabet : ℕ) (word : List ℕ)
    (h : y322RawEquationWordAllowed alphabet word) : List (Fin alphabet × Bool) :=
  word.pmap (fun packed hp => (⟨packed / 2, hp⟩, decide (packed % 2 = 1))) h

/-- A raw contextual substitution before its chronological and letter bounds are checked. -/
structure Y322RawContextEquationMove where
  /-- The referenced equation's chronological index. -/
  reference : ℕ
  /-- Whether to exchange that equation's sides. -/
  backward : Bool
  /-- Whether to invert both equation sides. -/
  inverted : Bool
  /-- Packed signed letters of the common left context. -/
  before : List ℕ
  /-- Packed signed letters of the common right context. -/
  after : List ℕ

/-- The referenced equation is earlier and every context letter belongs to the actual alphabet. -/
def Y322RawContextEquationMove.Allowed (alphabet earlier : ℕ)
    (move : Y322RawContextEquationMove) : Prop :=
  move.reference < earlier ∧ y322RawEquationWordAllowed alphabet move.before ∧
    y322RawEquationWordAllowed alphabet move.after

/-- Decode a contextual move while preserving its exact reference and signed context letters. -/
def y322RawContextEquationMoveDecode (alphabet earlier : ℕ)
    (move : Y322RawContextEquationMove) (h : move.Allowed alphabet earlier) :
    Y322ContextEquationMove (Fin alphabet) earlier :=
  ⟨⟨move.reference, h.1⟩, move.backward, move.inverted,
    y322RawEquationWordDecode alphabet move.before h.2.1,
    y322RawEquationWordDecode alphabet move.after h.2.2⟩

/-- Literal source references or lists of chronological contextual substitutions. -/
inductive Y322RawContextJustification
  | source (reference : ℕ)
  | contexts (moves : List Y322RawContextEquationMove)

/-- Every literal source and earlier-equation reference must satisfy its own exact bounds. -/
def Y322RawContextJustification.Allowed (alphabet sources earlier : ℕ) :
    Y322RawContextJustification → Prop
  | .source reference => reference < sources
  | .contexts moves => ∀ move ∈ moves, move.Allowed alphabet earlier

/-- A literal claimed equation together with its raw contextual derivation data. -/
structure Y322RawContextCertificate where
  /-- Packed signed letters of the claimed left-hand side. -/
  left : List ℕ
  /-- Packed signed letters of the claimed right-hand side. -/
  right : List ℕ
  /-- The literal source or chronological contextual substitution chain. -/
  justification : Y322RawContextJustification

/-- All claimed letters, source references and prior-equation references have their exact bounds. -/
def Y322RawContextCertificate.Allowed (alphabet sources earlier : ℕ)
    (certificate : Y322RawContextCertificate) : Prop :=
  y322RawEquationWordAllowed alphabet certificate.left ∧
    y322RawEquationWordAllowed alphabet certificate.right ∧
    certificate.justification.Allowed alphabet sources earlier

/-- Decode a finite literal derivation after checking its actual chronological reference bounds. -/
def y322RawContextJustificationDecode (alphabet sources earlier : ℕ)
    (justification : Y322RawContextJustification)
    (h : justification.Allowed alphabet sources earlier) :
    Fin sources ⊕ List (Y322ContextEquationMove (Fin alphabet) earlier) :=
  match justification with
  | .source reference => .inl ⟨reference, h⟩
  | .contexts moves => .inr
      (moves.pmap (fun move hm => y322RawContextEquationMoveDecode alphabet earlier move hm) h)

/-- Decode the exact claimed equation and its bound-checked finite contextual derivation. -/
def y322RawContextCertificateDecode (alphabet sources earlier : ℕ)
    (certificate : Y322RawContextCertificate) (h : certificate.Allowed alphabet sources earlier) :
    Y322WordEquation (Fin alphabet) ×
      (Fin sources ⊕ List (Y322ContextEquationMove (Fin alphabet) earlier)) :=
  (⟨y322RawEquationWordDecode alphabet certificate.left h.1,
      y322RawEquationWordDecode alphabet certificate.right h.2.1⟩,
    y322RawContextJustificationDecode alphabet sources earlier certificate.justification h.2.2)

/-- Exact finite alphabet bounds of a packed word are decidable. -/
instance y322RawEquationWordAllowedDecidable (alphabet : ℕ) (word : List ℕ) :
    Decidable (y322RawEquationWordAllowed alphabet word) := by
  unfold y322RawEquationWordAllowed
  infer_instance

/-- Exact chronological and alphabet bounds of a raw context move are decidable. -/
instance y322RawContextEquationMoveAllowedDecidable (alphabet earlier : ℕ)
    (move : Y322RawContextEquationMove) : Decidable (move.Allowed alphabet earlier) := by
  unfold Y322RawContextEquationMove.Allowed
  infer_instance

/-- Exact source and earlier-equation bounds of a raw derivation are decidable. -/
instance y322RawContextJustificationAllowedDecidable (alphabet sources earlier : ℕ)
    (justification : Y322RawContextJustification) :
    Decidable (justification.Allowed alphabet sources earlier) := by
  cases justification <;> unfold Y322RawContextJustification.Allowed <;> infer_instance

/-- All exact finite bounds of a raw equation certificate are decidable. -/
instance y322RawContextCertificateAllowedDecidable (alphabet sources earlier : ℕ)
    (certificate : Y322RawContextCertificate) :
    Decidable (certificate.Allowed alphabet sources earlier) := by
  unfold Y322RawContextCertificate.Allowed
  infer_instance

/-- Decode a fully bound-checked literal table as an exact acyclic contextual equation program. -/
def y322RawContextProgram {size : ℕ} (alphabet sources : ℕ)
    (raw : Fin size → Y322RawContextCertificate)
    (h : ∀ i, (raw i).Allowed alphabet sources i.val) :
    Y322ContextEquationProgram (Fin alphabet) (Fin sources) size :=
  fun i => y322RawContextCertificateDecode alphabet sources i.val (raw i) (h i)

/-- The raw chronological move reference is preserved exactly by the checked decoder. -/
theorem y322RawContextEquationMoveDecode_reference (alphabet earlier : ℕ)
    (move : Y322RawContextEquationMove) (h : move.Allowed alphabet earlier) :
    (y322RawContextEquationMoveDecode alphabet earlier move h).reference.val = move.reference := rfl

/-- The raw source reference is preserved exactly by the checked decoder. -/
theorem y322RawContextJustificationDecode_source (alphabet sources earlier reference : ℕ)
    (h : (Y322RawContextJustification.source reference).Allowed alphabet sources earlier) :
    y322RawContextJustificationDecode alphabet sources earlier (.source reference) h =
      Sum.inl ⟨reference, h⟩ := rfl

/-- Every packed signed letter is retained exactly in the decoded finite-alphabet word. -/
theorem y322RawEquationWordDecode_values (alphabet : ℕ) (word : List ℕ)
    (h : y322RawEquationWordAllowed alphabet word) :
    (y322RawEquationWordDecode alphabet word h).map
      (fun letter => 2 * letter.1.val + if letter.2 then 1 else 0) = word := by
  unfold y322RawEquationWordAllowed at h
  induction word with
  | nil => rfl
  | cons packed rest ih =>
    simp only [y322RawEquationWordDecode, List.pmap_cons, List.map_cons]
    congr 1
    · simp only [decide_eq_true_eq]
      split_ifs <;> omega
    · exact ih (fun n hn => h n (List.mem_cons_of_mem packed hn))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
