/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_LanglandsTunnell_HonestLDatum.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import MathlibExt.Analysis.Complex.BoundedOnStrips

@[expose] public section

noncomputable section

open Complex Polynomial

namespace LanglandsTunnell

/-- An L-datum: Euler factors, dual factors, archimedean factors,
abscissa, centre, and degree. -/
structure LDatum (ι : Type*) where

  norm : ι → ℕ

  euler : ι → ℂ[X]

  dual : ι → ℂ[X]

  gammaR : Multiset ℂ

  gammaC : Multiset ℂ

  gammaRDual : Multiset ℂ

  gammaCDual : Multiset ℂ

  abscissa : ℝ

  center : ℝ

  degree : ℕ

namespace LDatum

variable {ι : Type*} (D : LDatum ι)

/-- The L-function attached to an L-datum. -/
def LFun (s : ℂ) : ℂ :=
  ∏' i, ((D.euler i).eval ((D.norm i : ℂ) ^ (-s)))⁻¹

/-- The dual L-function attached to an L-datum. -/
def LFunDual (s : ℂ) : ℂ :=
  ∏' i, ((D.dual i).eval ((D.norm i : ℂ) ^ (-s)))⁻¹

/-- The archimedean factor attached to an L-datum. -/
def archFactor (s : ℂ) : ℂ :=
  (D.gammaR.map fun μ => Gammaℝ (s + μ)).prod * (D.gammaC.map fun μ => Gammaℂ (s + μ)).prod

/-- The dual archimedean factor attached to an L-datum. -/
def archFactorDual (s : ℂ) : ℂ :=
  (D.gammaRDual.map fun μ => Gammaℝ (s + μ)).prod *
    (D.gammaCDual.map fun μ => Gammaℂ (s + μ)).prod

/-- A bad factor built from a multiset of local polynomials. -/
def badFactor (bad : Multiset (ℕ × ℂ[X])) (s : ℂ) : ℂ :=
  (bad.map fun x => x.2.eval ((x.1 : ℂ) ^ (-s))).prod

/-- Bad data is a multiset of local factors, each indexed by a natural number at least two
and with constant term one. -/
def IsBadData (bad : Multiset (ℕ × ℂ[X])) : Prop :=
  ∀ x ∈ bad, 2 ≤ x.1 ∧ x.2.coeff 0 = 1

/-- An L-datum is well formed when its local and archimedean data
satisfy the recorded bounds. -/
def WellFormed : Prop :=
  (∀ i, 2 ≤ D.norm i) ∧
  (∀ i, (D.euler i).coeff 0 = 1 ∧ (D.euler i).natDegree ≤ D.degree ∧
    (D.dual i).coeff 0 = 1 ∧ (D.dual i).natDegree ≤ D.degree) ∧
  (∀ μ ∈ D.gammaR, -μ.re ≤ D.abscissa) ∧ (∀ μ ∈ D.gammaC, -μ.re ≤ D.abscissa) ∧
  (∀ μ ∈ D.gammaRDual, -μ.re ≤ D.abscissa) ∧ (∀ μ ∈ D.gammaCDual, -μ.re ≤ D.abscissa)

/-- An L-datum converges when its Euler products converge and do not
vanish to the right of the abscissa. -/
def Converges : Prop :=
  ∀ s : ℂ, D.abscissa < s.re →
    Summable (fun i => ‖(D.euler i).eval ((D.norm i : ℂ) ^ (-s)) - 1‖) ∧
    Summable (fun i => ‖(D.dual i).eval ((D.norm i : ℂ) ^ (-s)) - 1‖) ∧
    D.LFun s ≠ 0 ∧ D.LFunDual s ≠ 0

/-- An L-datum is nice when it is well formed and convergent and has
the recorded functional equation. -/
def IsNice : Prop :=
  D.WellFormed ∧ D.Converges ∧
  ∃ (bad badDual : Multiset (ℕ × ℂ[X])) (ε : ℂ) (N : ℝ) (Λ Λd : ℂ → ℂ),
    IsBadData bad ∧ IsBadData badDual ∧ 0 < N ∧
    Differentiable ℂ Λ ∧ Differentiable ℂ Λd ∧
    BoundedOnStrips Λ ∧ BoundedOnStrips Λd ∧
    (∀ s : ℂ, D.abscissa < s.re → Λ s * badFactor bad s = D.archFactor s * D.LFun s) ∧
    (∀ s : ℂ, D.abscissa < s.re →
      Λd s * badFactor badDual s = D.archFactorDual s * D.LFunDual s) ∧
    (∀ s : ℂ, Λ s = ε * (N : ℂ) ^ ((D.center : ℂ) - s) * Λd (2 * (D.center : ℂ) - s))

@[simp] theorem badFactor_zero (s : ℂ) : badFactor 0 s = 1 := by
  simp [badFactor]

theorem isBadData_zero : IsBadData 0 := fun _ h => (Multiset.notMem_zero _ h).elim

theorem archFactor_of_gammaC_eq_zero (hC : D.gammaC = 0) (s : ℂ) :
    D.archFactor s = (D.gammaR.map fun μ => Gammaℝ (s + μ)).prod := by
  simp [archFactor, hC]

end LDatum

end LanglandsTunnell
