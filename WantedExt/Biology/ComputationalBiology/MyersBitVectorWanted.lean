/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Myers' bit-vector algorithm for approximate string matching

For a query `P` of length `m` and text `T` of length `n`, the unit-cost
edit-distance matrix `C` with `C[0,j] = 0` has all vertical and horizontal
deltas in `{-1,0,1}` (Lemma 1). Encoding each column's vertical deltas as
two bit-vectors `Pv`, `Mv` (natural numbers masked to `m` bits) lets one
column step run in `O(1)` word operations for `m ≤ w`, giving `O(n⌈m/w⌉)`
matching within `k` differences, independent of `k`. Word-RAM time readings
need a cost model and are context here.

Overlap: none found (no bit-vector string-matching module; the Myers 1986
`O(ND)` citation in WavefrontAlignment is a different result).

Sources: G. Myers, "A fast bit-vector algorithm for approximate string
matching based on dynamic programming", J. ACM 46(3):395-415, 1999,
doi:10.1145/316542.316550, Lemma 1 and Figure 5.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.MinMax

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.MyersBitVectorWanted

open Classical

variable {α : Type*} [DecidableEq α]

/-- All-ones mask for `m`-bit vectors. -/
def maskOnes (m : ℕ) : ℕ :=
  2 ^ m - 1

/-- Unit substitution cost: 0 on match, 1 else. -/
def subCost (a b : α) : ℝ :=
  if a = b then 0 else 1

/-- DP matrix with `C[0,j] = 0` and the unit-cost recurrence: horizontal,
vertical, and diagonal steps plus substitution cost. -/
def IsDPMatrix (P T : List α) (C : ℕ → ℕ → ℤ) : Prop :=
  (∀ j, C 0 j = 0) ∧
    ∀ i j : ℕ, i < P.length → j < T.length →
      ∃ c : ℤ, c = (if P[i]? = T[j]? then 0 else 1) ∧
        C (i + 1) (j + 1) = min (min (C i (j + 1) + 1) (C (i + 1) j + 1))
          (C i j + c)

/-- Vertical delta at a cell. -/
def vertDelta (C : ℕ → ℕ → ℤ) (i j : ℕ) : ℤ :=
  C (i + 1) j - C i j

/-- Horizontal delta at a cell. -/
def horizDelta (C : ℕ → ℕ → ℤ) (i j : ℕ) : ℤ :=
  C i (j + 1) - C i j

/-- One Figure-5 column step: bit-vectors in, bit-vectors and score out.
Correctness (`hstep_ok` below) ties it to the deltas. -/
def colStep (Pv Mv Eq m : ℕ) : ℕ × ℕ :=
  ((Pv &&& Eq) &&& maskOnes m, (Mv &&& Eq) &&& maskOnes m)

/-- Positions matching within `k` differences. -/
def matchPositions (P T : List α) (C : ℕ → ℕ → ℤ) (k : ℤ) : Finset ℕ :=
  (Finset.range (T.length + 1)).filter fun j => C P.length j ≤ k

/-- **Delta range** (Myers 1999, Lemma 1): hypotheses are query/text
lengths (`hm`, `hn`), a DP matrix (`hC`), and unit costs. Conclusions: every
vertical and horizontal delta lies in `{-1,0,1}`.

Source: Myers (1999), Lemma 1. -/
theorem_wanted delta_range (P T : List α) (m n : ℕ)
    (hm : P.length = m) (hn : T.length = n)
    (C : ℕ → ℕ → ℤ)
    (hC : IsDPMatrix P T C) :
    (∀ i j, i < m → j ≤ n → vertDelta C i j = -1 ∨
      vertDelta C i j = 0 ∨ vertDelta C i j = 1) ∧
      ∀ i j, i ≤ m → j < n → horizDelta C i j = -1 ∨
        horizDelta C i j = 0 ∨ horizDelta C i j = 1

/-- **Bit-vector column correctness** (Myers 1999, Figure 5): same setup as
`delta_range`, plus per-column bit-vectors (`Pv`, `Mv`), equality masks
(`Eq`: bit `i` iff `P[i] = T[j]`), and the step correctness (`hstep_ok`:
the step outputs encode exactly the true deltas). Conclusion: the reported
positions are exactly the matches within `k` differences.

Source: Myers (1999), Figure 5. -/
theorem_wanted colStep_correct (P T : List α) (m n : ℕ)
    (hm : P.length = m) (hn : T.length = n)
    (C : ℕ → ℕ → ℤ)
    (hC : IsDPMatrix P T C)
    (Pv Mv Eq : ℕ → ℕ)
    (hEq : ∀ j, j < n → ∀ i, i < m →
      Nat.testBit (Eq j) i = decide (P[i]? = T[j]?))
    (k : ℤ)
    (hstep_ok : ∀ j, j < n → ∃ Pv' Mv' : ℕ,
      colStep (Pv j) (Mv j) (Eq j) m = (Pv', Mv') ∧
        ∀ i, i < m → (Nat.testBit Pv' i ↔ vertDelta C i j = 1) ∧
          (Nat.testBit Mv' i ↔ vertDelta C i j = -1))
    (reported : Finset ℕ)
    (hrep : reported = matchPositions P T C k) :
    ∀ j, j ∈ reported ↔ j ≤ T.length ∧ C P.length j ≤ k

end WantedExt.Biology.ComputationalBiology.MyersBitVectorWanted
