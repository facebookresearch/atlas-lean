/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Computability.ContextFreeGrammar
public import Cslib.Algorithms.Lean.TimeM

/-!
# Indexed CYK primitives

The executable table is indexed by length and start position, never by
substring equality. Cells contain at most one nonterminal per production.
Costs use an abstract word model, not Lean persistent-array runtime costs.
Indices, symbol handles and addresses must fit words. Guarded array reads
(including bounds/default selection), replacement, index arithmetic, list
cons/tests, Boolean operations and equation dispatch cost one. Array
initialization costs its number of entries plus one; list-to-array conversion
costs twice its length plus one. Variables, field/pointer projections,
existing literals and return packaging are free administrative operations.
The `TimeM` counters are ghost instrumentation, not recursively charged work.

`termCost` and `ntCost` explicitly price terminal and nonterminal equality;
unit equality uses both equal to one. No runtime bound on an arbitrary
`DecidableEq` implementation is asserted. The scalar overheads below cover
the remaining primitive operations, including unsuccessful scans. Rules are
supplied as a list enumeration of the existing `ContextFreeGrammar` rules;
the correctness theorem checks its membership, without a third carrier.

Lean arrays provide executable values and get/set semantics. This is NOT a
proof that persistent-array updates avoid copying, nor a bit-complexity or
wall-clock bound for Lean evaluation. Such a claim needs a separate runtime
refinement. No substring creation, substring comparison, set insertion or
list-table search is hidden in the executable code.

`CYKIndexed.Correctness` bridges to canonical `cykAccepts` and language
semantics; `CYKIndexed.Cost` proves an explicit fixed-grammar cubic bound.
`CYKIndexed.Encoded` includes charged preparation of canonical `EncodedCFG`.
-/

@[expose] public section

namespace Cslib.Language.CYKIndexed

open Cslib.Algorithms.Lean

variable {T N : Type*} [DecidableEq N]

/-- Full membership scan, charging equality and list/control operations. -/
def member (eqCost : ℕ) (a : N) : List N → TimeM ℕ Bool
  | [] => ⟨false, 1⟩
  | b :: bs =>
      let rest := member eqCost a bs
      ⟨decide (a = b) || rest.ret, rest.time + eqCost + 3⟩

/-- The charged scan has ordinary list-membership semantics. -/
@[simp] theorem member_ret (eqCost : ℕ) (a : N) (xs : List N) :
    (member eqCost a xs).ret = true ↔ a ∈ xs := by
  induction xs with
  | nil => simp [member]
  | cons b bs ih => simp [member, ih]

/-- Two bounded array reads; invalid indices denote an empty cell. -/
def lookup (tbl : Array (Array (List N))) (i len : ℕ) : List N :=
  (tbl[len]?.getD #[])[i]?.getD []

/-- Scan split positions `1,...,count`, with two table reads per split.
The 16 units cover four array reads, bounds/default tests, index arithmetic,
Boolean combinations and recursion control. -/
def splits (eqCost : ℕ) (tbl : Array (Array (List N)))
    (i len : ℕ) (b c : N) : ℕ → TimeM ℕ Bool
  | 0 => ⟨false, 1⟩
  | k + 1 =>
      let rest := splits eqCost tbl i len b c k
      let left := member eqCost b (lookup tbl i (k + 1))
      let right := member eqCost c (lookup tbl (i + (k + 1)) (len - (k + 1)))
      ⟨rest.ret || (left.ret && right.ret),
        rest.time + left.time + right.time + 16⟩

/-- Every successful scan names a split in exactly the scanned interval. -/
theorem splits_ret (eqCost : ℕ) (tbl : Array (Array (List N)))
    (i len : ℕ) (b c : N) (count : ℕ) :
    (splits eqCost tbl i len b c count).ret = true ↔
      ∃ k, 0 < k ∧ k ≤ count ∧ b ∈ lookup tbl i k ∧
        c ∈ lookup tbl (i + k) (len - k) := by
  induction count with
  | zero => simp [splits]
  | succ count ih =>
      simp only [splits, Bool.or_eq_true, Bool.and_eq_true, member_ret, ih]
      constructor
      · rintro (⟨k, hk, hle, hb, hc⟩ | ⟨hb, hc⟩)
        · exact ⟨k, hk, by omega, hb, hc⟩
        · exact ⟨count + 1, by omega, le_rfl, hb, hc⟩
      · rintro ⟨k, hk, hle, hb, hc⟩
        by_cases h : k ≤ count
        · exact Or.inl ⟨k, hk, h, hb, hc⟩
        · have heq : k = count + 1 := by omega
          subst k
          exact Or.inr ⟨hb, hc⟩

variable [DecidableEq T]

/-- Test a production output without constructing or comparing substrings.
Pattern inspection is bounded (at most three cons and two symbol tags). -/
def fits (termCost ntCost : ℕ) (w : Array T)
    (tbl : Array (Array (List N))) (i len : ℕ) :
    List (Symbol T N) → TimeM ℕ Bool
  | [.terminal a] =>
      ⟨decide (len = 1) && decide (w[i]? = some a), termCost + 12⟩
  | [.nonterminal b, .nonterminal c] =>
      let r := splits ntCost tbl i len b c (len - 1)
      ⟨r.ret, r.time + 8⟩
  | _ => ⟨false, 8⟩

/-- Scan every production once, retaining its input exactly when it fits.
Duplicates are allowed; no set insertion or uncharged deduplication occurs. -/
def cell (termCost ntCost : ℕ) (w : Array T)
    (tbl : Array (Array (List N))) (i len : ℕ) :
    List (ContextFreeRule T N) → TimeM ℕ (List N)
  | [] => ⟨[], 1⟩
  | r :: rs =>
      let f := fits termCost ntCost w tbl i len r.output
      let rest := cell termCost ntCost w tbl i len rs
      ⟨if f.ret then r.input :: rest.ret else rest.ret,
        f.time + rest.time + 5⟩

/-- Membership in a computed cell names an actual scanned production. -/
theorem mem_cell (termCost ntCost : ℕ) (w : Array T)
    (tbl : Array (Array (List N))) (i len : ℕ)
    (rs : List (ContextFreeRule T N)) (a : N) :
    a ∈ (cell termCost ntCost w tbl i len rs).ret ↔
      ∃ r ∈ rs, r.input = a ∧
        (fits termCost ntCost w tbl i len r.output).ret = true := by
  induction rs with
  | nil => simp [cell]
  | cons r rs ih =>
      simp only [cell]
      split <;>
        simp only [List.mem_cons, ih, exists_eq_or_imp] <;> aesop

/-- Build one row in increasing start-position order. Each cell is evaluated
once against the already completed shorter rows. -/
def row (termCost ntCost : ℕ) (w : Array T)
    (tbl : Array (Array (List N))) (len : ℕ)
    (rs : List (ContextFreeRule T N)) (i : ℕ) :
    ℕ → TimeM ℕ (List (List N))
  | 0 => ⟨[], 1⟩
  | count + 1 =>
      let c := cell termCost ntCost w tbl i len rs
      let rest := row termCost ntCost w tbl len rs (i + 1) count
      ⟨c.ret :: rest.ret, c.time + rest.time + 4⟩

/-- Fill rows `1,...,depth` in a fixed outer array of size `w.size + 1`.
Row conversion is linear; the outer update is an indexed primitive. -/
def table (termCost ntCost : ℕ) (w : Array T)
    (rs : List (ContextFreeRule T N)) :
    ℕ → TimeM ℕ (Array (Array (List N)))
  | 0 => ⟨Array.replicate (w.size + 1) #[], w.size + 4⟩
  | depth + 1 =>
      let prev := table termCost ntCost w rs depth
      let next := row termCost ntCost w prev.ret (depth + 1) rs 0
        (w.size + 1)
      ⟨prev.ret.set! (depth + 1) next.ret.toArray,
        prev.time + next.time + 2 * (w.size + 1) + 8⟩

/-- Scan start epsilon rules; output emptiness is a single list-tag test. -/
def epsilon (ntCost : ℕ) (start : N) :
    List (ContextFreeRule T N) → TimeM ℕ Bool
  | [] => ⟨false, 1⟩
  | r :: rs =>
      let rest := epsilon ntCost start rs
      ⟨(decide (r.input = start) && r.output.isEmpty) || rest.ret,
        rest.time + ntCost + 6⟩

/-- The charged indexed recognizer. The nonempty branch pays for the input
length scan, conversion, completed table, final lookup and membership. -/
def recognizes (termCost ntCost : ℕ) (start : N)
    (rs : List (ContextFreeRule T N)) (w : List T) : TimeM ℕ Bool :=
  match w with
  | [] =>
      let r := epsilon ntCost start rs
      ⟨r.ret, r.time + 1⟩
  | _ :: _ =>
      let a := w.toArray
      let tbl := table termCost ntCost a rs a.size
      let r := member ntCost start (lookup tbl.ret 0 a.size)
      ⟨r.ret, tbl.time + r.time + 3 * w.length + 12⟩

end Cslib.Language.CYKIndexed
