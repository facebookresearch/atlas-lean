/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The q-TSPP theorem

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.QTSPP` — q_tspp (manifest `manifests/problems/q_tspp.toml`, rev 1, submitter Timothy Y. Chow, status draft) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.QTSPPWanted` namespace. Mathematical
statements are unchanged. Source: Koutschan, Kauers, and Zeilberger (2011), Theorem 1. DOI: 10.1073/pnas.1019186108
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.UpperLower.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.QTSPPWanted
/-!
# The q-TSPP theorem

Statement of the Kauers-Koutschan-Zeilberger q-TSPP theorem.
-/

open scoped BigOperators

namespace QTSPP

noncomputable section

/- A Cell is a 3-tuple of nonnegative integers -/
abbrev Cell := ℕ × ℕ × ℕ

/- Cells are partially ordered via the product order -/
theorem cell_le_iff (a b : Cell) :
    a ≤ b ↔
      a.1 ≤ b.1 ∧
      a.2.1 ≤ b.2.1 ∧
      a.2.2 ≤ b.2.2 := by
  rfl

/- A box of size n is the set {0,1,...,n-1}^3-/
def box (n : ℕ) : Finset Cell :=
  (Finset.range n).product
    ((Finset.range n).product (Finset.range n))

/- A finite set of Cells is totally symmetric if
   it is invariant under the natural action of S_3 -/
def IsTotallySymmetric (π : Finset Cell) : Prop :=
  ∀ i j k : ℕ, (i, j, k) ∈ π →
    (i, k, j) ∈ π ∧
    (j, i, k) ∈ π ∧
    (j, k, i) ∈ π ∧
    (k, i, j) ∈ π ∧
    (k, j, i) ∈ π

/- A totally symmetric plane partition (TSPP) is
   a finite set of Cells that is an order ideal
   (in the natural partial order on Cells) and is
   also totally symmetric. Mathlib's "IsLowerSet"
   already captures the notion of an order ideal.-/
def IsTSPP (π : Finset Cell) : Prop :=
  IsLowerSet (π : Set Cell) ∧ IsTotallySymmetric π

/- tspps is the set of all TSPPs inside a box of size n,
   including the empty TSPP -/
def tspps (n : ℕ) : Finset (Finset Cell) := by
  classical
  exact (box n).powerset.filter IsTSPP

/- sortedTriples n is the set of all Cells (i, j, k)
   in the box of size n such that i ≤ j ≤ k -/
def sortedTriples (n : ℕ) : Finset Cell :=
  (box n).filter (fun c => c.1 ≤ c.2.1 ∧ c.2.1 ≤ c.2.2)

/- The q-TSPP theorem enumerates TSPPs by
   the number of orbits; this is equivalent
   to the number of cells whose coordinates
   are in weakly increasing order -/
def orbitCount (π : Finset Cell) : ℕ :=
  (π.filter (fun c => c.1 ≤ c.2.1 ∧ c.2.1 ≤ c.2.2)).card

/- The coordinateSum of a Cell (i,j,k) is i+j+k -/
def coordinateSum (c : Cell) : ℕ :=
  c.1 + c.2.1 + c.2.2

local notation "q" => (Polynomial.X : Polynomial ℤ)

/- The left-hand side of the q-TSPP theorem is
   the generating polynomial for TSPPs by orbitCount -/
def generatingPolynomial (n : ℕ) : Polynomial ℤ :=
  ∑ π ∈ tspps n, q ^ (orbitCount π)

/- To avoid any worries about division by zero, we
   multiply by the denominator of the right-hand side.
   Our Cell coordinates start from 0, while the usual
   statement of the q-TSPP theorem starts from 1, so
   care is needed to get the exponent of q right. -/
/-- Source: Koutschan, Kauers, and Zeilberger (2011), Theorem 1. DOI: 10.1073/pnas.1019186108 Via leanprover/lean-eval@38361be, problem `q_tspp`. -/
public theorem_wanted q_tspp (n : ℕ) :
    generatingPolynomial n *
      (∏ c ∈ sortedTriples n,
        (1 - q ^ (coordinateSum c + 1))) =
    ∏ c ∈ sortedTriples n,
      (1 - q ^ (coordinateSum c + 2))

end

end QTSPP

end MathlibExt.Combinatorics.QTSPPWanted
