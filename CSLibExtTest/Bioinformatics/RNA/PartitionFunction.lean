/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.RNA.PartitionFunction
public meta import CSLibExt.Bioinformatics.RNA.PartitionFunction

/-!
# Semiring folding and McCaskill partition function tests

Executed fixtures (each `#guard` fails the build on a disagreement):
* Waterman's numbers for `m = 0` are the Motzkin numbers (OEIS A001006) and for `m = 1` the
  Stein–Waterman numbers (OEIS A004148), and agree with the counting-semiring inside value on
  `n` points.
* On all `A`/`C`/`G`/`U` sequences of length at most `4` and `m ∈ {0, 1, 3}`: the
  counting-semiring inside value equals a brute-force count of structures, the min-plus inside
  value with weight `-1` equals minus the Nussinov maximum, and the inside value over `ℚ` with
  position-dependent weights equals the brute-force weighted sum.
* On an eight-base sequence: McCaskill's outside value times the pair weight times the inside
  value equals the brute-force weight of the structures containing each candidate pair, and
  the resulting pair probabilities of each base sum to at most `1`.

Non-vacuity: the hypotheses `i + m < j` and `CanPair pair s i j` of the outside theorem hold
for a concrete pair. Boundary: positions outside the sequence never pair, and with a negative
weight the total weight can vanish, making `pairProb` the junk value `0`.
-/

namespace Cslib.Bioinformatics.RNA.PartitionFunction

/-- RNA bases. -/
inductive Base
  | A | C | G | U
  deriving DecidableEq, Repr

open Base

/-- Watson–Crick and `G–U` wobble complementarity. -/
def wc : Base → Base → Bool
  | A, U | U, A | G, C | C, G | G, U | U, G => true
  | _, _ => false

/-- Complementarity as a relation. -/
abbrev wcP (a b : Base) : Prop := wc a b = true

/-- Every pair of points may pair (Waterman's counting problem). -/
abbrev anyPair (_ _ : Unit) : Prop := True

/-- The sequence `GGGAAAUCC`. -/
def s₀ : List Base := [G, G, G, A, A, A, U, C, C]

-- Non-vacuity of the outside theorem's hypotheses: `(0, 8)` is a candidate pair for `m = 3`.
example : 0 + 3 < 8 ∧ CanPair wcP s₀ 0 8 := ⟨by decide, by decide⟩

-- Boundary: position `9` is outside `s₀`, so it pairs with nothing.
example : ¬ CanPair wcP s₀ 0 9 := by decide

-- Boundary: two adenines do not pair.
example : ¬ CanPair wcP s₀ 3 4 := by decide

/-! ### Counting -/

-- Motzkin numbers (OEIS A001006) for `m = 0`.
#guard (List.range 10).map (watermanNumber 0) = [1, 1, 2, 4, 9, 21, 51, 127, 323, 835]

-- Stein–Waterman numbers (OEIS A004148) for `m = 1`.
#guard (List.range 10).map (watermanNumber 1) = [1, 1, 1, 2, 4, 8, 17, 37, 82, 185]

-- `m = 3`, the usual RNA minimum hairpin.
#guard (List.range 10).map (watermanNumber 3) = [1, 1, 1, 1, 1, 2, 4, 8, 16, 32]

#guard (List.range 12).all fun n => watermanNumber 0 n == MetaMathlibExt.motzkinNumber n

#guard [0, 1, 2, 3].all fun m => (List.range 9).all fun n =>
  inside anyPair m (List.replicate n ()) (fun _ _ => (1 : ℕ)) 0 n == watermanNumber m n

/-! ### Brute force over all structures -/

/-- Decidable form of `IsStructure` on candidate pairs, for brute force. -/
def isStructureB (m : ℕ) (s : List Base) (P : List (ℕ × ℕ)) : Bool :=
  P.all (fun p => decide (p.1 + m < p.2) && decide (CanPair wcP s p.1 p.2)) &&
  P.all fun p => P.all fun q => (p == q || (p.1 != q.1 && p.1 != q.2 && p.2 != q.1 &&
    p.2 != q.2)) && !(decide (p.1 < q.1) && decide (q.1 < p.2) && decide (p.2 < q.2))

/-- All secondary structures of `s`, by brute force over subsets of the candidate pairs
(`i + m < j`, complementary bases). -/
def bruteStructures (m : ℕ) (s : List Base) : List (List (ℕ × ℕ)) :=
  let cands := ((List.range s.length).flatMap fun i =>
    (List.range s.length).map fun j => (i, j)).filter fun p =>
      decide (p.1 + m < p.2) && decide (CanPair wcP s p.1 p.2)
  cands.sublists.filter (isStructureB m s)

/-- All sequences of length at most `n`. -/
def seqs : ℕ → List (List Base)
  | 0 => [[]]
  | n + 1 => [] :: (seqs n).flatMap fun w => [A :: w, C :: w, G :: w, U :: w]

/-- Position-dependent rational weights. -/
def wq (i j : ℕ) : ℚ := (i + 2 * j + 1 : ℚ) / 7

/-- The weight of a list of pairs. -/
def wtq (P : List (ℕ × ℕ)) : ℚ := (P.map fun p => wq p.1 p.2).prod

-- Counting semiring: the inside value counts the structures.
#guard [0, 1, 3].all fun m => (seqs 4).all fun s =>
  inside wcP m s (fun _ _ => (1 : ℕ)) 0 s.length == (bruteStructures m s).length

-- Min-plus semiring with weight `-1`: minus the Nussinov maximum.
#guard [0, 1, 3].all fun m => (seqs 4).all fun s =>
  MinTropical.untrop (inside wcP m s (fun _ _ => MinTropical.trop ((-1 : ℤ) : WithTop ℤ)) 0
    s.length) == ((-(Nussinov.nussinov wcP m s : ℤ) : ℤ) : WithTop ℤ)

-- Sum-product semiring: the weighted sum over all structures.
#guard [0, 1, 3].all fun m => (seqs 4).all fun s =>
  inside wcP m s wq 0 s.length == ((bruteStructures m s).map wtq).sum

/-! ### Outside values and pair probabilities -/

/-- An eight-base sequence with several competing helices. -/
def s₁ : List Base := [G, A, C, U, A, G, U, C]

/-- The candidate pairs of `s₁` for minimum hairpin `m`. -/
def cands₁ (m : ℕ) : List (ℕ × ℕ) :=
  ((List.range 8).flatMap fun i => (List.range 8).map fun j => (i, j)).filter fun p =>
    decide (p.1 + m < p.2) && decide (CanPair wcP s₁ p.1 p.2)

#guard (cands₁ 1).length = 10

-- McCaskill's outside recursion: the weight of the structures containing each candidate pair.
#guard [0, 1, 3].all fun m => (cands₁ m).all fun p =>
  outside wcP m s₁ wq p.1 p.2 * wq p.1 p.2 * inside wcP m s₁ wq (p.1 + 1) (p.2 - (p.1 + 1)) ==
    (((bruteStructures m s₁).filter fun P => P.contains p).map wtq).sum

/-- McCaskill's pair probability from the inside and outside values (`0` off candidates). -/
def probq (m i j : ℕ) : ℚ :=
  if decide (i + m < j) && decide (CanPair wcP s₁ i j) then
    outside wcP m s₁ wq i j * wq i j * inside wcP m s₁ wq (i + 1) (j - (i + 1)) /
      inside wcP m s₁ wq 0 8
  else 0

-- Each base is paired with probability at most `1`.
#guard [0, 1, 3].all fun m => (List.range 8).all fun i =>
  ((List.range 8).map fun j => probq m i j + probq m j i).sum ≤ 1

/-! ### Junk value outside the domain `0 ≤ w` -/

-- With the negative weight `-1` on `GC` (`m = 0`), the total weight is `1 + (-1) = 0`, so the
-- pair probability is the junk value `x / 0 = 0`; `one_le_sum_weight` rules this out for
-- nonnegative weights.
example : pairProb wcP 0 [G, C] (fun _ _ => -1) 0 1 = 0 := by
  have hc : CanPair wcP [G, C] 0 1 := by decide
  rw [pairProb_eq_outside wcP 0 [G, C] _ 0 1 (by decide) hc]
  have hz : inside wcP 0 [G, C] (fun _ _ => (-1 : ℝ)) 0 [G, C].length = 0 := by
    simp [inside, hc]
  rw [hz, div_zero]

#print axioms inside_eq_sum
#print axioms outside_mul_eq_sum
#print axioms inside_minTropical
#print axioms card_structures_eq_watermanNumber
#print axioms watermanNumber_zero_eq_motzkinNumber
#print axioms sum_pairProb_le_one

end Cslib.Bioinformatics.RNA.PartitionFunction
