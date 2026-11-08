/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.BipartiteMatching
public meta import CSLibExt.Algorithms.Lean.Graph.BipartiteMatching

/-!
# Maximum bipartite matching: tests

Executed fixtures: each run checks that the results of `maxMatching` and `hopcroftKarp` are
matchings (pairs are edges, no vertex twice) whose size equals a brute-force maximum over all
matchings, and that `2 ⌊√b⌋ + 2` phases already reach that maximum
(`card_le_hopcroftKarpAux_sqrt`). Each run also checks every phase: its path lengths all equal
`firstFreeRound + 1` (`length_of_mem_phase`); every alternating chain of that length from an
unmatched right vertex shares a vertex with one of its paths (`phase_maximal`); every layer after
its flip is contained in the same layer before (`layers_flip_phase_subset`); and the next phase's
`firstFreeRound` is strictly larger (`lt_firstFreeRound_flip_phase`). It throws otherwise, and
prints the number of phases and single augmentations and the path lengths per phase.
Closed checks: the correctness theorems applied to a fixture.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BipartiteMatching

/-- The pairs of a partner array, as natural numbers. -/
private def pairList {a b : ℕ} (mate : Fin b → Option (Fin a)) : List (ℕ × ℕ) :=
  (List.finRange b).filterMap fun j => (mate j).map fun i => (i.val, j.val)

/-- Brute force: the largest matching, left vertex by left vertex. -/
private def bruteMax {a b : ℕ} (adj : Fin a → List (Fin b)) : ℕ :=
  let rec go : List (Fin a) → List (Fin b) → ℕ
    | [], _ => 0
    | i :: is, used =>
        ((adj i).filter (· ∉ used)).foldl (fun best j => max best (go is (j :: used) + 1))
          (go is used)
  go (List.finRange a) []

/-- The number of phases Hopcroft–Karp runs, and the number of augmentations the one-path method
runs, from the empty matching. -/
private def rounds {a b : ℕ} (adj : Fin a → List (Fin b)) : ℕ × ℕ :=
  let rec phases : ℕ → (Fin b → Option (Fin a)) → ℕ
    | 0, _ => 0
    | f + 1, m => match hkStep adj m with
      | none => 0
      | some m' => phases f m' + 1
  let rec augs : ℕ → (Fin b → Option (Fin a)) → ℕ
    | 0, _ => 0
    | f + 1, m => match augment adj m with
      | none => 0
      | some m' => augs f m' + 1
  (phases (b + 1) fun _ => none, augs (b + 1) fun _ => none)

/-- All alternating chains of `L` pairs from the right vertex `z` that end at an unmatched left
vertex (the candidate shortest augmenting paths, before distinctness). -/
private def chains {a b : ℕ} (adj : Fin a → List (Fin b)) (mate : Fin b → Option (Fin a)) :
    ℕ → Fin b → List (List (Fin a × Fin b))
  | 0, _ => []
  | L + 1, z =>
    ((List.finRange a).filter fun i => decide (z ∈ adj i ∧ mate z ≠ some i)).flatMap fun i =>
      match (List.finRange b).find? (fun j' => decide (mate j' = some i)) with
      | none => if L = 0 then [[(i, z)]] else []
      | some j' => (chains adj mate L j').map ((i, z) :: ·)

/-- The path lengths of each phase from the empty matching, whether every one equals
`firstFreeRound + 1`, and whether every chain of that length from an unmatched right vertex meets
a path of the phase. -/
private def phaseLengths {a b : ℕ} (adj : Fin a → List (Fin b)) : List (List ℕ) × Bool :=
  let rec go : ℕ → (Fin b → Option (Fin a)) → List (List ℕ) × Bool
    | 0, _ => ([], true)
    | f + 1, m =>
      let Ps := phase adj m
      if Ps.isEmpty then ([], true)
      else
        let ok := match firstFreeRound adj m with
          | some d =>
            let lefts := Ps.flatten.map Prod.fst
            let rights := Ps.flatten.map Prod.snd
            (Ps.all fun P => P.length == d + 1) &&
              ((List.finRange b).filter fun j => decide (m j = none)).all fun j =>
                (chains adj m (d + 1) j).all fun Q =>
                  Q.any fun q => q.1 ∈ lefts || q.2 ∈ rights
          | none => false
        let m' := flip m Ps.flatten
        let mono := (List.range (a + 2)).all fun k =>
          decide ((layers adj m' k).1 ⊆ (layers adj m k).1) &&
            decide ((layers adj m' k).2 ⊆ (layers adj m k).2)
        let longer := match firstFreeRound adj m, firstFreeRound adj m' with
          | some d, some d' => decide (d < d')
          | _, _ => true
        let (rest, okRest) := go f m'
        (Ps.map List.length :: rest, ok && mono && longer && okRest)
  go (b + 1) fun _ => none

private def isMatchingList {a b : ℕ} (adj : Fin a → List (Fin b)) (ps : List (ℕ × ℕ)) : Bool :=
  (ps.all fun p => (List.finRange a).any fun i => i.val == p.1 &&
    (adj i).any fun j => j.val == p.2) && (ps.map (·.1)).Nodup && (ps.map (·.2)).Nodup

private def check (label : String) (a b : ℕ) (adj : Fin a → List (Fin b)) : IO Unit := do
  let ps := pairList (maxMatching adj)
  let hk := pairList (hopcroftKarp adj)
  let hkSqrt := pairList (hopcroftKarpAux adj (2 * Nat.sqrt b + 2) fun _ => none)
  let best := bruteMax adj
  let (np, na) := rounds adj
  let (lens, lensOk) := phaseLengths adj
  unless isMatchingList adj ps && isMatchingList adj hk && ps.length == best &&
      hk.length == best && hkSqrt.length == best && lensOk do
    throw (IO.userError s!"{label}: matchings {ps} and {hk}, brute-force maximum {best}, \
      phase path lengths {lens}")
  IO.println s!"{label}: matching {ps}, size {ps.length} = maximum {best}; Hopcroft–Karp {hk} \
    in {np} phases ({na} single augmentations); phase path lengths {lens}"

/-- A graph where the greedy first choice must be undone: left `0` can take `0` or `1`, left `1`
only `0`. -/
private def swap : Fin 2 → List (Fin 2)
  | 0 => [0, 1]
  | 1 => [0]

#eval check "swap" 2 2 swap
#eval check "path of length 5" 3 3
  (fun i => if i.val = 0 then [0] else [⟨i.val - 1, by omega⟩, ⟨i.val, by omega⟩])
#eval check "complete 3 × 4" 3 4 (fun _ => List.finRange 4)
#eval check "Hall violation" 4 4 (fun i => if i.val < 3 then [0, 1] else [2, 3])
#eval check "no edges" 3 2 (fun _ => [])
#eval check "pseudo-random 6 × 6" 6 6
  (fun i => (List.finRange 6).filter fun j => (i.val * 5 + j.val * 3) % 7 < 3)
#eval check "pseudo-random 7 × 5" 7 5
  (fun i => (List.finRange 5).filter fun j => (i.val * i.val + 2 * j.val) % 5 = 1)
#eval check "perfect 6 × 6 (one phase)" 6 6 (fun i => [i])
-- The first phase matches `i` to `i` for `i < 3`; the second needs the long path from `3`
-- through all of them.
#eval check "chain needing a long path" 4 4
  (fun i => if h : i.val < 3 then [i, ⟨i.val + 1, by omega⟩] else [0])
-- Left `i < 12` is adjacent to right `i` and `i + 1`, left `12` only to right `0`.
#eval check "ladder of choices" 13 13
  (fun i => if h : i.val < 12 then [⟨i.val, by omega⟩, ⟨i.val + 1, by omega⟩] else [0])
#eval check "pseudo-random 8 × 8" 8 8
  (fun i => (List.finRange 8).filter fun j => (3 * i.val + 5 * j.val + i.val * j.val) % 4 = 0)

example : IsMatching swap (pairs (maxMatching swap)) := isMatching_maxMatching
example {M : Finset (Fin 2 × Fin 2)} (hM : IsMatching swap M) :
    M.card ≤ (pairs (maxMatching swap)).card :=
  card_le_maxMatching hM

example : IsMatching swap (pairs (hopcroftKarp swap)) := isMatching_hopcroftKarp
example {M : Finset (Fin 2 × Fin 2)} (hM : IsMatching swap M) :
    M.card ≤ (pairs (hopcroftKarp swap)).card :=
  card_le_hopcroftKarp hM

/-- A graph where one phase finds three disjoint augmenting paths: a perfect matching of
`3 × 3` with `adj i = [i]`. -/
example : (phase (fun i : Fin 3 => [i]) fun _ => none).length = 3 := by decide

#print axioms card_le_hopcroftKarpAux_sqrt
#print axioms mul_card_sub_le
#print axioms layers_flip_phase_subset
#print axioms lt_firstFreeRound_flip_phase
#print axioms phase_maximal
#print axioms length_of_mem_phase
#print axioms le_length_of_isAugmentingPath
#print axioms isMatching_hopcroftKarp
#print axioms card_le_hopcroftKarp
#print axioms isMatching_maxMatching
#print axioms card_le_maxMatching
#print axioms card_le_of_no_free

end Cslib.Algorithms.Lean.BipartiteMatching
