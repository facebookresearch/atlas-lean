/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Acyclic E7 elementary proofs using only equations from the original C431 Coxeter relators. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431E7ProofData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The program starts with 171 genuine source equations, then 185 literal rewrite rows. -/
def y431E7ProofProgram : Y322EquationProgram (Fin 9) (Fin 171) 356 := fun i =>
  if h : i.val < 171 then
    ⟨y431CoxeterEquation ⟨i.val, h⟩, .source ⟨i.val, h⟩⟩
  else
    let row : Fin 185 := ⟨i.val - 171, by omega⟩
    ⟨(y431E7ProofData row).1, .substitutions
      ((y431E7ProofData row).2.map fun p =>
        ⟨⟨p.1.val, by have hp := p.1.isLt; omega⟩, false, false, p.2⟩)⟩

/-- Every literal source-equation seed is valid against its unchanged exact source equation. -/
theorem y431E7ProofProgram_seed_checked (i : Fin 356) (hi : i.val < 171) :
    (y431E7ProofProgram i).Checked y431CoxeterEquation
      (fun a => (y431E7ProofProgram (y322ProgramPrior i a)).equation) := by
  simp only [y431E7ProofProgram, dite_eq_left hi, Y322EquationCertificate.Checked,
    y322EquationsSameReduction]
  constructor <;> trivial

/-- Each candidate rewrite row is checked by literal substitutions of strictly earlier sources. -/
def y431E7ProofRowChecked (row : Fin 185) : Prop :=
  let i : Fin 356 := ⟨171 + row.val, by omega⟩
  (y431E7ProofProgram i).Checked y431CoxeterEquation
    (fun a => (y431E7ProofProgram (y322ProgramPrior i a)).equation)

/-- All original-source elementary proof row checks are decidable by finite word operations. -/
instance y431E7ProofRowCheckedDecidable (row : Fin 185) :
    Decidable (y431E7ProofRowChecked row) := by
  unfold y431E7ProofRowChecked
  dsimp only
  have hi : ¬ (171 + row.val < 171) := by omega
  simp only [y431E7ProofProgram, dite_eq_right hi, Y322EquationCertificate.Checked]
  infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
