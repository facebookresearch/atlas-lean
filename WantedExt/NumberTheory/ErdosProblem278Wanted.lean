/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 278
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Order.Monotone.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem278Wanted

/-! Source record `EP-278` (Erdős Problems), statement frozen from
https://www.erdosproblems.com/278 (status OPEN on 2026-09-18).

Clause map: "density of covered integers" is compared via covered counts over
one full period (the moduli product; all choices share the moduli, so counts
are comparable); "the minimum is achieved when all `aᵢ` are equal" is
existence of a common residue below all moduli minimizing the count. The
"maximum density" question has no conjectured value and is not formalized. -/

open scoped Classical in
/-- Covered count over one full period for a residue choice. -/
noncomputable def coveredCount (r : ℕ) (n : Fin r → ℕ)
    (a : (i : Fin r) → Fin (n i)) : ℕ :=
  let P := Finset.univ.prod n
  ((Finset.range P).filter
    (fun x => ∃ i : Fin r, Nat.ModEq (n i) x (a i).val)).card

/-- Erdős Problem 278: the minimum covered density is achieved by an
all-equal residue choice. -/
def conjecture : Prop :=
  ∀ r : ℕ, ∀ n : Fin r → ℕ, StrictMono n → (∀ i, 1 ≤ n i) →
    ∃ c : ℕ, ∃ h : ∀ i, c < n i,
      ∀ a : (i : Fin r) → Fin (n i),
        coveredCount r n (fun i => ⟨c, h i⟩) ≤ coveredCount r n a

/--
Resolved true: The formalized second question (the minimum covered density is attained when all
residues a_i are equal) is settled: erdosproblems.com/278 (checked 2026-10-22) records that
Simpson (Discrete Math. 1986) showed every choice of residues covers density at least Σ 1/n_i −
Σ 1/[n_i,n_j] + ⋯, with equality when all a_i are equal. The first question (the maximum
density) is open-ended and not formalized. Source: R. J. Simpson, Exact coverings of the
integers by arithmetic progressions, Discrete Mathematics 59 (1986), 181-190. Moved from
`OpenConjectures/NumberTheory/ErdosProblem278`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem278Wanted
