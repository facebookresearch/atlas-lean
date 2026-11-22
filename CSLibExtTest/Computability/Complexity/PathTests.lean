/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Path
public meta import CSLibExt.Computability.Complexity.Path

/-! Tests for the PATH encoding and the marking algorithm. -/

namespace Cslib.Complexity.Path.Tests

/-- All vertex sequences of length `k` over `0, …, n - 1`. -/
private def seqs (n : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (seqs n k).flatMap fun p => (List.range n).map (· :: p)

/-- Brute force: `s = t`, or some sequence of at most `n - 1` inner vertices links them. -/
private def reach (n : ℕ) (es : List (ℕ × ℕ)) (s t : ℕ) : Bool :=
  decide (s < n) && decide (t < n) &&
    ((List.range n).any fun k => (seqs n k).any fun p =>
      let w := s :: p ++ [t]
      (w.zip w.tail).all fun e => e ∈ es) || (decide (s < n) && s == t)

-- The encoding and its parser.
#guard encodeP 1 0 2 [(0, 1)] = [true, false, false, true, true, false, false, true, false]
#guard decodeP (encodeP 2 0 3 [(0, 1), (2, 2)]) = some (2, 0, 3, [(0, 1), (2, 2)])
#guard decodeP [] = none && decodeP [false] = none && decodeP [false, false] = none
#guard decodeP (encodeP 0 1 2 [] ++ [true]) = none
-- A chain listed backwards needs `n - 1` passes; `s = t`; targets out of range; ignored arcs.
#guard pathCheck (encodeP 0 3 4 [(2, 3), (1, 2), (0, 1)])
#guard !pathCheck (encodeP 3 0 4 [(2, 3), (1, 2), (0, 1)])
#guard pathCheck (encodeP 2 2 3 []) && !pathCheck (encodeP 3 3 3 [])
#guard !pathCheck (encodeP 0 1 1 [(0, 1)]) && !pathCheck (encodeP 0 2 2 [(0, 5), (5, 1)])
#guard !pathCheck [] && !pathCheck [true, false]
-- Sweep: every digraph on 3 vertices without loops, every `s`, `t`, both edge orders.
#guard (List.range 64).all fun g =>
  let es := ([(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)].zip
    ((List.range 6).map fun i => g / 2 ^ i % 2 == 1)).filterMap fun p => if p.2 then p.1 else none
  (List.range 3).all fun s => (List.range 3).all fun t =>
    pathCheck (encodeP s t 3 es) == reach 3 es s t &&
      pathCheck (encodeP s t 3 es.reverse) == reach 3 es s t

end Cslib.Complexity.Path.Tests
