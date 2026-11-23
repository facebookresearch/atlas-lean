/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 939, question 3
-/
module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem939Question3Wanted

/-! Source record `UM-00002394-Q003`. -/
/-- `n > 0` is 3-powerful: `p ^ 3 ∣ n` for every prime `p ∣ n`. -/
def IsThreePowerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 3 ∣ n

/-- There are infinitely many triples of pairwise coprime 3-powerful numbers with
`a + b = c`. -/
def conjecture : Prop :=
  Set.Infinite { t : ℕ × ℕ × ℕ |
    IsThreePowerful t.1 ∧
    IsThreePowerful t.2.1 ∧
    IsThreePowerful t.2.2 ∧
    Nat.Coprime t.1 t.2.1 ∧
    Nat.Coprime t.1 t.2.2 ∧
    Nat.Coprime t.2.1 t.2.2 ∧
    t.1 + t.2.1 = t.2.2 }

-- Carried source audit `UM-00002394-Q003` (see the Moved/ record).

/--
Resolved true: Proved: Nitaj (Bull. London Math. Soc. 27 (1995), 317-318) constructed infinitely
many triples of coprime 3-powerful numbers a, b, c with a + b = c, as erdosproblems.com/939
(checked 2026-10-22) records; Cohn (1998) and Walsh (arXiv:2404.03970) give further
constructions. Coprime solutions of a + b = c are pairwise coprime, as in the Lean statement.
Source: Abderrahmane Nitaj, On a Conjecture of Erdős on 3-Powerful Numbers, Bulletin of the
London Mathematical Society 27 (1995), no. 4, 317–318, https://doi.org/10.1112/blms/27.4.317;
Thomas F. Bloom, Erdős Problem #939, https://www.erdosproblems.com/939; P. G. Walsh, A question
of Erdős on 3-powerful numbers and an elliptic curve analogue of the Ankeny-Artin-Chowla
conjecture, arXiv:2404.03970 (2024), https://arxiv.org/abs/2404.03970. Moved from
`OpenConjectures/NumberTheory/ErdosProblem939Question3`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem939Question3Wanted
