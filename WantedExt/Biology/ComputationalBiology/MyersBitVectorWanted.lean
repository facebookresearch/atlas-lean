/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Myers' bit-vector algorithm for approximate string matching

For a pattern `P` of length `m` and a text `T` of length `n`, the approximate-matching
dynamic-programming matrix `C` has `C[0, j] = 0` (a match may start anywhere in the text),
`C[i, 0] = i`, and the unit-cost edit-distance recurrence
`C[i+1, j+1] = min(C[i, j+1] + 1, C[i+1, j] + 1, C[i, j] + [P_{i+1} ≠ T_{j+1}])`.
The pattern matches with at most `k` differences ending at text position `j` exactly when
`C[m, j] ≤ k`.

**Lemma 1** (Myers 1999). Every vertical delta `C[i+1, j] - C[i, j]` and every horizontal delta
`C[i, j+1] - C[i, j]` lies in `{-1, 0, 1}`.

**Algorithm** (Myers 1999). Encode the vertical deltas of column `j` by two `m`-bit vectors
`Pv` (deltas `+1`) and `Mv` (deltas `-1`), start from `Pv = 1^m`, `Mv = 0^m` and score `m`, and
update them for each text character with a constant number of bitwise operations and one
addition, using the match mask `Eq` of that character (bit `i` set exactly when `P_{i+1}` equals
it). The score `C[m, j]` changes by the top bit of the horizontal deltas, and position `j` is
reported when the score is at most `k`. The reported positions are exactly the positions
`1 ≤ j ≤ n` with `C[m, j] ≤ k`. That correctness statement rests on Lemma 1, so only Lemma 1 is
stated here, together with the algorithm.

The update below is Myers' column recurrence in the standard formulation (`Xv`, `Xh`, `Ph`, `Mh`
with the carry-propagating addition). Bit vectors are natural numbers below `2^m`, with the sum
and the shifts reduced modulo `2^m`, so a single word of width `m` is modelled. The running-time
claims (`O(1)` word operations per column for `m ≤ w`, `O(n⌈m/w⌉)` overall, and the `O(kn/w)`
expected bound) need a word-RAM cost model and are not stated.

Sources: G. Myers, "A fast bit-vector algorithm for approximate string matching based on
dynamic programming", J. ACM 46(3):395-415, 1999, doi:10.1145/316542.316550, Lemma 1 and the
column-update algorithm.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Int.Basic
public import Mathlib.Order.MinMax

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.MyersBitVectorWanted

variable {α : Type*} [DecidableEq α]

/-- The approximate-matching dynamic-programming matrix: `dp P T 0 j = 0`,
`dp P T i 0 = i`, and `dp P T (i+1) (j+1)` is the minimum of `dp P T i (j+1) + 1`,
`dp P T (i+1) j + 1` and `dp P T i j` plus `0` if `P[i] = T[j]` and `1` otherwise. -/
def dp (P T : List α) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | i + 1, 0 => i + 1
  | i + 1, j + 1 =>
    min (min (dp P T i (j + 1) + 1) (dp P T (i + 1) j + 1))
      (dp P T i j + if P[i]? = T[j]? then 0 else 1)
termination_by i j => (i, j)

/-- The match mask of the character `c`: bit `i` is set exactly when `P[i] = c`. -/
def eqMask (P : List α) (c : α) : ℕ :=
  ((List.range P.length).filter fun i => P[i]? = some c).foldr (fun i acc => 2 ^ i + acc) 0

/-- **One column update of the bit-vector algorithm.** For a pattern of length `m`, the update
takes the state `(Pv, Mv, score)` and the match mask `Eq` of the next text character, where
`Eq`, `Pv` and `Mv` are `m`-bit vectors, that is naturals below `2^m`. The update does not reduce
these inputs, so wider ones are outside its contract. With `mask = 2^m - 1` and `¬x = mask ⊕ x`:
`Xv = Eq ∨ Mv`, `Xh = ((((Eq ∧ Pv) + Pv) ∧ mask) ⊕ Pv) ∨ Eq`, `Ph = Mv ∨ ¬(Xh ∨ Pv)`,
`Mh = Pv ∧ Xh`; the score increases by one if bit `m - 1` of `Ph` is set and otherwise
decreases by one if bit `m - 1` of `Mh` is set; then `Ph` and `Mh` are shifted left by one
(without carry-in, since `C[0, j] = 0`) and reduced modulo `2^m`, and the new state is
`Pv' = Mh ∨ ¬(Xv ∨ Ph)`, `Mv' = Ph ∧ Xv`, again `m`-bit vectors. -/
def step (m Eq : ℕ) (s : ℕ × ℕ × ℤ) : ℕ × ℕ × ℤ :=
  let mask := 2 ^ m - 1
  let Pv := s.1
  let Mv := s.2.1
  let Xv := Eq ||| Mv
  let Xh := ((((Eq &&& Pv) + Pv) &&& mask) ^^^ Pv) ||| Eq
  let Ph := Mv ||| (mask ^^^ (Xh ||| Pv))
  let Mh := Pv &&& Xh
  let score := if Ph.testBit (m - 1) then s.2.2 + 1
    else if Mh.testBit (m - 1) then s.2.2 - 1 else s.2.2
  let Ph' := (Ph <<< 1) &&& mask
  let Mh' := (Mh <<< 1) &&& mask
  (Mh' ||| (mask ^^^ (Xv ||| Ph')), Ph' &&& Xv, score)

/-- Scan the remaining text `T`, whose first character is at text position `j + 1`, from the
state `s`, reporting each position whose score after its update is at most `k`. -/
def scan (P : List α) (k : ℤ) : List α → ℕ → ℕ × ℕ × ℤ → List ℕ
  | [], _, _ => []
  | c :: T, j, s =>
    let s' := step P.length (eqMask P c) s
    (if s'.2.2 ≤ k then [j + 1] else []) ++ scan P k T (j + 1) s'

/-- The positions reported by the bit-vector algorithm: start from `Pv = 2^m - 1`, `Mv = 0` and
score `m`, and scan the text from position `1`. -/
def myersMatches (P T : List α) (k : ℤ) : List ℕ :=
  scan P k T 0 (2 ^ P.length - 1, 0, P.length)

/-- **Deltas lie in `{-1, 0, 1}`** (Myers 1999, Lemma 1). For a pattern `P` and a text `T`, every
vertical delta `dp P T (i+1) j - dp P T i j` with `i < |P|` and `j ≤ |T|`, and every horizontal
delta `dp P T i (j+1) - dp P T i j` with `i ≤ |P|` and `j < |T|`, is `-1`, `0` or `1`.

Source: G. Myers, J. ACM 46 (1999) 395-415, Lemma 1.

Source: J. Kärkkäinen, *String Processing Algorithms*, lecture notes, University of Helsinki,
Autumn 2016, lecture 7, Lemma 3.15,
<https://www.cs.helsinki.fi/u/tpkarkka/teach/16-17/SPA/lecture07.pdf>. -/
theorem_wanted delta_mem (P T : List α) :
    (∀ i j, i < P.length → j ≤ T.length →
      ((dp P T (i + 1) j : ℤ) - dp P T i j) ∈ ({-1, 0, 1} : Set ℤ)) ∧
    ∀ i j, i ≤ P.length → j < T.length →
      ((dp P T i (j + 1) : ℤ) - dp P T i j) ∈ ({-1, 0, 1} : Set ℤ)

end WantedExt.Biology.ComputationalBiology.MyersBitVectorWanted
