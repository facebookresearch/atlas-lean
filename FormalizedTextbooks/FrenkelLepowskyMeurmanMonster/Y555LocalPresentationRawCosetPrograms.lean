/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite letter, source, and chronological bounds for actual right-coset certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationCosetChains
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawContextPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Literal source-equation contexts or right contexts of fixed and earlier coset claims. -/
inductive Y522RawCosetMove
  | equation (source : ℕ) (backward inverted : Bool) (before after : List ℕ)
  | fixed (source : ℕ) (backward : Bool) (after : List ℕ)
  | prior (reference : ℕ) (backward : Bool) (after : List ℕ)

/-- Every source, prior reference, and signed letter must satisfy its actual finite bound. -/
def Y522RawCosetMove.Allowed (alphabet equations fixed earlier : ℕ) : Y522RawCosetMove → Prop
  | .equation source _ _ before after => source < equations ∧
      y322RawEquationWordAllowed alphabet before ∧ y322RawEquationWordAllowed alphabet after
  | .fixed source _ after => source < fixed ∧ y322RawEquationWordAllowed alphabet after
  | .prior reference _ after => reference < earlier ∧ y322RawEquationWordAllowed alphabet after

/-- Decode a source or right-coset step only after all of its exact finite bounds are proved. -/
def y522RawCosetMoveDecode (alphabet equations fixed earlier : ℕ)
    (move : Y522RawCosetMove) (h : move.Allowed alphabet equations fixed earlier) :
    Y522CosetMove (Fin alphabet) (Fin equations) (Fin fixed) earlier :=
  match move with
  | .equation source backward inverted before after =>
      .equation ⟨source, h.1⟩ backward inverted
        (y322RawEquationWordDecode alphabet before h.2.1)
        (y322RawEquationWordDecode alphabet after h.2.2)
  | .fixed source backward after =>
      .fixed ⟨source, h.1⟩ backward (y322RawEquationWordDecode alphabet after h.2)
  | .prior reference backward after =>
      .prior ⟨reference, h.1⟩ backward (y322RawEquationWordDecode alphabet after h.2)

/-- A literal claimed coset word pair together with its finite chain of source consequences. -/
structure Y522RawCosetCertificate where
  /-- Packed signed letters on the claimed left side. -/
  left : List ℕ
  /-- Packed signed letters on the claimed right side. -/
  right : List ℕ
  /-- Exact actual-equation and right-coset derivation moves. -/
  moves : List Y522RawCosetMove

/-- All claimed and contextual letters and all source and prior references must be bounded. -/
def Y522RawCosetCertificate.Allowed (alphabet equations fixed earlier : ℕ)
    (certificate : Y522RawCosetCertificate) : Prop :=
  y322RawEquationWordAllowed alphabet certificate.left ∧
    y322RawEquationWordAllowed alphabet certificate.right ∧
      ∀ move ∈ certificate.moves, move.Allowed alphabet equations fixed earlier

/-- Decode every literal claim and move without truncation or out-of-range fallback. -/
def y522RawCosetCertificateDecode (alphabet equations fixed earlier : ℕ)
    (certificate : Y522RawCosetCertificate)
    (h : certificate.Allowed alphabet equations fixed earlier) :
    Y322WordEquation (Fin alphabet) ×
      List (Y522CosetMove (Fin alphabet) (Fin equations) (Fin fixed) earlier) :=
  (⟨y322RawEquationWordDecode alphabet certificate.left h.1,
      y322RawEquationWordDecode alphabet certificate.right h.2.1⟩,
    certificate.moves.pmap
      (fun move hm => y522RawCosetMoveDecode alphabet equations fixed earlier move hm) h.2.2)

/-- The exact finite bounds of a raw coset move are decidable. -/
instance y522RawCosetMoveAllowedDecidable (alphabet equations fixed earlier : ℕ)
    (move : Y522RawCosetMove) : Decidable (move.Allowed alphabet equations fixed earlier) := by
  cases move <;> unfold Y522RawCosetMove.Allowed <;> infer_instance

/-- The exact finite bounds of a complete raw coset certificate are decidable. -/
instance y522RawCosetCertificateAllowedDecidable (alphabet equations fixed earlier : ℕ)
    (certificate : Y522RawCosetCertificate) :
    Decidable (certificate.Allowed alphabet equations fixed earlier) := by
  unfold Y522RawCosetCertificate.Allowed
  infer_instance

/-- An actual finite coset program decoded after all source and chronological bounds are checked. -/
def y522RawCosetProgram {size : ℕ} (alphabet equations fixed : ℕ)
    (raw : Fin size → Y522RawCosetCertificate)
    (h : ∀ i, (raw i).Allowed alphabet equations fixed i.val) :
    Y522CosetProgram (Fin alphabet) (Fin equations) (Fin fixed) size :=
  fun i => y522RawCosetCertificateDecode alphabet equations fixed i.val (raw i) (h i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
