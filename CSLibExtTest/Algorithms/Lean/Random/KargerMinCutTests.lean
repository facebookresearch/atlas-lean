/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Random.KargerMinCut
public meta import CSLibExt.Algorithms.Lean.Random.KargerMinCut

/-!
# Karger tests

Exact success probabilities (`successProb`, a rational) on small multigraphs, each compared with
Karger's bound `2 / (n (n - 1))` for the minimum cut size `k` found by brute force over all
vertex subsets; the run throws if the bound fails or the state is invalid. Fixtures: the 4-cycle
(`k = 2`; contracting a cycle always leaves a cycle, so the probability is `1`), `K₄` (`k = 3`),
two triangles joined by a bridge (`k = 1`, the bridge), a path, and a multigraph with three
parallel edges. On those five fixtures, every value below `k` is also checked to have probability
`0` at fuel `0`, `1`, `n` and `n + 2`, covering immediate return and early fuel exhaustion. Three
further fixtures have minimum cut `0`: two isolated vertices stop at once (`verts ≤ 2`),
the empty graph on four vertices stops at once (`edges = []`), and two disjoint edges contract
twice down to a zero cut before stopping; with `k = 0` there is no value below the
minimum, so none of the three is undershoot evidence. A separate check confirms that `K₄` can return a
value above its minimum cut. A second fixture counts the minimum cuts by brute force and checks
the `n (n - 1) / 2` bound, each cut's survival probability (`surviveProb`) against
`2 / (n (n - 1))`, and that they add up to at most `1`; on the 5-cycle the bound is attained.
The `repeatSuccessProb` checks use the independent-runs closed form.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Karger

/-- The minimum cut size by brute force over the subsets of `{0, …, n-1}` (bit masks). -/
private def bruteMinCut (n : ℕ) (edges : List (ℕ × ℕ)) : ℕ :=
  let masks := (List.range (2 ^ n)).filter fun m => m != 0 && m != 2 ^ n - 1
  (masks.map fun m => cutSize edges fun v => Nat.testBit m v).foldl min edges.length

private def check (label : String) (n : ℕ) (edges : List (ℕ × ℕ)) : IO Unit := do
  let st : State ℕ := ⟨List.range n, edges⟩
  let valid := edges.all fun e => e.1 < n && e.2 < n && e.1 != e.2
  let k := bruteMinCut n edges
  let p := successProb k n st
  let bound : ℚ := 2 / ((n : ℚ) * (n - 1))
  unless valid && bound ≤ p do
    throw (IO.userError s!"{label}: k = {k}, probability {p}, bound {bound}")
  IO.println s!"{label}: n = {n}, |E| = {edges.length}, min cut {k}, probability {p} ≥ {bound}"

#eval check "4-cycle" 4 [(0, 1), (1, 2), (2, 3), (3, 0)]
#eval check "K4" 4 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
#eval check "two triangles and a bridge" 6
  [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (2, 3)]
#eval check "path on 4 vertices" 4 [(0, 1), (1, 2), (2, 3)]
#eval check "parallel edges" 3 [(0, 1), (0, 1), (1, 0), (1, 2)]

/-- Count the minimum cuts by brute force (one bit mask per partition: the side containing
vertex `0`), check `2 · count ≤ n (n - 1)`, that each survives with probability at least
`2 / (n (n - 1))`, and that the survival probabilities add up to at most `1`. -/
private def checkCount (label : String) (n : ℕ) (edges : List (ℕ × ℕ)) : IO Unit := do
  let st : State ℕ := ⟨List.range n, edges⟩
  let k := bruteMinCut n edges
  let cuts := ((List.range (2 ^ n)).filter fun m => m % 2 == 1 && m != 2 ^ n - 1).filter
    fun m => cutSize edges (fun v => Nat.testBit m v) == k
  let probs := cuts.map fun m => surviveProb (fun v => Nat.testBit m v) n st
  let bound : ℚ := 2 / ((n : ℚ) * (n - 1))
  let total := probs.sum
  unless 2 * cuts.length ≤ n * (n - 1) && probs.all (bound ≤ ·) && total ≤ 1 do
    throw (IO.userError s!"{label}: {cuts.length} minimum cuts, probabilities {probs}")
  IO.println s!"{label}: {cuts.length} minimum cuts ≤ n (n - 1) / 2 = {n * (n - 1) / 2}; \
    each survives with probability ≥ {bound}, total {total} ≤ 1"

#eval checkCount "5-cycle (the bound is attained)" 5 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
#eval checkCount "K4" 4 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
#eval checkCount "two triangles and a bridge" 6
  [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (2, 3)]
#eval checkCount "path on 4 vertices" 4 [(0, 1), (1, 2), (2, 3)]
#eval checkCount "parallel edges" 3 [(0, 1), (0, 1), (1, 0), (1, 2)]

#eval
  let st : State ℕ := ⟨List.range 4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]⟩
  IO.println s!"K4, independent-runs closed form at 6: {repeatSuccessProb 3 6 st} ≥ 1/2"

-- Independent-runs closed form at `c · n (n - 1) / 2` runs: at least `1 - (1/2)^c`.
#eval do
  let st : State ℕ := ⟨List.range 4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]⟩
  for c in [1, 2, 3] do
    let p := repeatSuccessProb 3 (6 * c) st
    unless 1 - (1 / 2 : ℚ) ^ c ≤ p do
      throw (IO.userError s!"K4, {6 * c} runs: {p} < 1 - (1/2)^{c}")
    IO.println s!"K4, {6 * c} runs: {p} ≥ 1 - (1/2)^{c} = {1 - (1 / 2 : ℚ) ^ c}"


example {V : Type} [DecidableEq V] (st : State V) (hv : st.Valid) {k : ℕ} (hmin : IsMinCut st k)
    (hn : 2 ≤ st.verts.length) :
    2 / ((st.verts.length : ℚ) * (st.verts.length - 1)) ≤ successProb k st.verts.length st :=
  successProb_ge st hv hmin hn

example {V : Type} [DecidableEq V] (st : State V) (hv : st.Valid) {k : ℕ} (hmin : IsMinCut st k)
    (hk : 1 ≤ k) (hn : 2 ≤ st.verts.length) (F : List (V → Bool))
    (hF : ∀ X ∈ F, IsCut st X ∧ cutSize st.edges X = k) (hd : F.Pairwise (DistinctOn st.verts)) :
    2 * F.length ≤ st.verts.length * (st.verts.length - 1) :=
  two_mul_length_minCuts_le st hv hmin hk hn F hF hd

-- every run returns at least the minimum cut size: `successProb j fuel st = 0` for each `j < k`,
-- at fuel `0`, `1`, `n` and `n + 2`, on all five fixtures with `k ≥ 1`
#eval do
  let fixtures : List (String × ℕ × List (ℕ × ℕ)) :=
    [("K4", 4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
     ("4-cycle", 4, [(0, 1), (1, 2), (2, 3), (3, 0)]),
     ("two triangles and a bridge", 6,
       [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (2, 3)]),
     ("path on 4 vertices", 4, [(0, 1), (1, 2), (2, 3)]),
     ("parallel edges", 3, [(0, 1), (0, 1), (1, 0), (1, 2)])]
  for (label, n, edges) in fixtures do
    let st : State ℕ := ⟨List.range n, edges⟩
    let k := bruteMinCut n edges
    for j in List.range k do
      for fuel in [0, 1, n, n + 2] do
        unless successProb j fuel st == 0 do
          throw (IO.userError s!"{label}: returns {j} < {k} with positive probability \
            at fuel {fuel}")
    IO.println s!"{label}: no run returns less than the minimum cut {k}"

-- Zero-minimum-cut fixtures (`k = 0`): two isolated vertices and the empty graph stop at
-- once; two disjoint edges contract twice down to a zero cut before stopping. With `k = 0`
-- there is no value below the minimum, so none of them is undershoot evidence.
#eval check "two isolated vertices" 2 []
#eval check "empty graph on four vertices" 4 []
#eval check "two disjoint edges" 4 [(0, 1), (2, 3)]

-- A non-minimum result can still occur; the new bound only excludes smaller results.
#eval do
  let st : State ℕ := ⟨List.range 4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]⟩
  let p := successProb 4 4 st
  unless 0 < p do
    throw (IO.userError s!"K4: expected positive probability of returning 4, got {p}")
  IO.println s!"K4: probability of returning 4 > minimum cut 3 is {p}"

-- The result is independent of the vertex universe and applies to every fuel value.
universe u

example {V : Type u} [DecidableEq V] (st : State V) (hv : st.Valid) {k : ℕ} (hmin : IsMinCut st k)
    (hn : 2 ≤ st.verts.length) {j : ℕ} (hj : j < k) (fuel : ℕ) :
    successProb j fuel st = 0 :=
  successProb_eq_zero_of_lt_minCut st hv hmin hn hj fuel

-- `repeatSuccessProb` is the independent-runs closed form by definition
example {V : Type u} [DecidableEq V] (k t : ℕ) (st : State V) :
    repeatSuccessProb k t st = 1 - (1 - successProb k st.verts.length st) ^ t := rfl

example {V : Type u} [DecidableEq V] (st : State V) (k : ℕ) :
    repeatSuccessProb k 0 st = 0 := by
  simp [repeatSuccessProb]

example {V : Type u} [DecidableEq V] (st : State V) (k : ℕ) :
    repeatSuccessProb k 1 st = successProb k st.verts.length st := by
  simp [repeatSuccessProb]

-- Empty states, including states over an empty vertex type, have no minimum cut.
example {V : Type u} (k : ℕ) : ¬ IsMinCut (⟨[], []⟩ : State V) k := by
  simp [IsMinCut, IsCut]

#print axioms successProb_eq_zero_of_lt
#print axioms successProb_eq_zero_of_lt_minCut
#print axioms successProb_ge
#print axioms surviveProb_ge
#print axioms sum_surviveProb_le_one
#print axioms two_mul_length_minCuts_le
#print axioms repeatSuccessProb_ge_half
#print axioms repeatSuccessProb_ge
#print axioms repeatSuccessProb_ge_one_sub_inv
#print axioms successProb_nonneg
#print axioms successProb_le_one
#print axioms cutSize_contract
#print axioms isMinCut_contract
#print axioms valid_contract
#print axioms sum_degree
#print axioms card_mul_le_two_mul_edges

end Cslib.Algorithms.Lean.Karger
