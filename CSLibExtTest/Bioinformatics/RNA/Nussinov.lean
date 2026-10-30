/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.RNA.Nussinov
public meta import CSLibExt.Bioinformatics.RNA.Nussinov

/-!
# Nussinov algorithm tests

Non-vacuity: a concrete two-pair structure on `GGGAAAUCC` with Watson–Crick pairing and
minimum loop length `3` satisfies `IsStructure` (checked by `decide`), and the empty structure
is a structure on every sequence. Boundary probes: a crossing set and a set sharing a position
are rejected, and a pair enclosing fewer than `m` positions is rejected. Executed fixtures: the
recursion's value on short sequences with `m = 0` and `m = 3`, and agreement with a brute-force
maximum over all subsets of candidate pairs on all `A`/`U`/`G`/`C` sequences of length at most
`4`, for `m ∈ {0, 1, 3}`. Each run throws on a disagreement.
-/

namespace Cslib.Bioinformatics.RNA.Nussinov

/-- RNA bases. -/
inductive Base
  | A | C | G | U
  deriving DecidableEq, Repr

open Base

/-- Watson–Crick complementarity. -/
def wc : Base → Base → Bool
  | A, U | U, A | G, C | C, G => true
  | _, _ => false

/-- The sequence `GGGAAAUCC`. -/
def s₀ : List Base := [G, G, G, A, A, A, U, C, C]

/-- Two nested pairs `G0–C8`, `G1–C7` closing the loop `GAAAU`. -/
def P₀ : Finset (ℕ × ℕ) := {(0, 8), (1, 7)}

-- Non-vacuity: a genuine structure with two pairs.
example : IsStructure (fun a b => wc a b = true) 3 s₀ P₀ := by
  refine ⟨by decide, fun p hp => ?_, by decide, by decide⟩
  simp only [P₀, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨G, C, rfl, rfl, rfl⟩
  · exact ⟨G, C, rfl, rfl, rfl⟩

-- The empty structure.
example {B : Type} (pair : B → B → Prop) (m : ℕ) (s : List B) : IsStructure pair m s ∅ :=
  ⟨by simp, by simp, by simp, by simp⟩

-- Rejected: crossing pairs `(0, 7)` and `(1, 8)`.
example : ¬ IsStructure (fun a b => wc a b = true) 3 s₀ {(0, 7), (1, 8)} := fun h =>
  absurd (h.noncrossing (0, 7) (by decide) (1, 8) (by decide)) (by decide)

-- Rejected: two pairs sharing position `8`.
example : ¬ IsStructure (fun a b => wc a b = true) 0 s₀ {(0, 8), (1, 8)} := fun h =>
  absurd (h.disjoint (0, 8) (by decide) (1, 8) (by decide) (by decide)) (by decide)

-- Rejected: the pair `(3, 6)` (`A–U`) encloses only two positions, fewer than `m = 3`.
example : ¬ IsStructure (fun a b => wc a b = true) 3 s₀ {(3, 6)} := fun h =>
  absurd (h.loop (3, 6) (by decide)) (by decide)

#guard nussinov (fun a b => wc a b = true) 0 s₀ = 3
#guard nussinov (fun a b => wc a b = true) 3 s₀ = 2
#guard nussinov (fun a b => wc a b = true) 0 [] = 0
#guard nussinov (fun a b => wc a b = true) 1 [G, C] = 0
#guard nussinov (fun a b => wc a b = true) 0 [G, C] = 1

/-- Decidable form of `IsStructure` on candidate pairs (`i < j < |s|`), for brute force. -/
def isStructureB (m : ℕ) (s : List Base) (P : List (ℕ × ℕ)) : Bool :=
  P.all (fun p => decide (p.1 + m < p.2) && match s[p.1]?, s[p.2]? with
    | some a, some b => wc a b
    | _, _ => false) &&
  P.all fun p => P.all fun q => (p == q || (p.1 != q.1 && p.1 != q.2 && p.2 != q.1 &&
    p.2 != q.2)) && !(decide (p.1 < q.1) && decide (q.1 < p.2) && decide (p.2 < q.2))

/-- The largest structure, by brute force over all subsets of the candidate pairs. -/
def bruteMax (m : ℕ) (s : List Base) : ℕ :=
  let cands := (List.range s.length).flatMap fun i =>
    ((List.range s.length).filter (i < ·)).map fun j => (i, j)
  (cands.sublists.filter (isStructureB m s)).foldr (fun P acc => max P.length acc) 0

/-- All sequences of length at most `n`. -/
def seqs : ℕ → List (List Base)
  | 0 => [[]]
  | n + 1 => [] :: (seqs n).flatMap fun w => [A :: w, C :: w, G :: w, U :: w]

#guard [0, 1, 3].all fun m => (seqs 4).all fun s =>
  nussinov (fun a b => wc a b = true) m s == bruteMax m s

end Cslib.Bioinformatics.RNA.Nussinov
