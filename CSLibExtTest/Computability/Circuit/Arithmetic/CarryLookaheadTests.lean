/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Circuit.Arithmetic.CarryLookahead
public meta import CSLibExt.Computability.Circuit.Arithmetic.CarryLookahead

/-!
# Carry-lookahead adder tests

Executed fixtures: the outputs of the Kogge-Stone adder (CSLib's `Circuit.eval`) are compared with
`BitVec.adc` on every input of the 1-bit adder with `K = 0` and `K = 1` levels. CSLib's evaluator
recomputes a gate every time it is read, so its cost grows exponentially with the gate count and
already the 16-gate 2-bit adder is out of reach; the Kogge-Stone network is exercised instead
through its specification: `gpSpec` after `claLevels n` levels is checked to give `BitVec.carry`
on all inputs of widths up to 6. The gate counts are checked against `5 n + 3 n K` and the
ripple-carry depths against `rippleCarryAdder_depth`. Each run throws on a mismatch. Closed checks
instantiate the theorems, including the 64-bit adder's carry and depth.
-/

namespace Cslib.Circuits

open CarryLookahead

private meta def agrees (n K : ℕ) (a b : ℕ) (c : Bool) : Bool :=
  let x := BitVec.ofNat n a
  let y := BitVec.ofNat n b
  let out := (carryLookaheadAdder n K).eval arithInterpretation (rcaInput x y c)
  let r := BitVec.adc x y c
  (List.range n).all (fun i => if h : i < n then out ⟨i, by omega⟩ == r.2.getLsbD i else true) &&
    out ⟨n, by omega⟩ == r.1

#eval do
  for K in [0, 1] do
    for a in [0, 1] do
      for b in [0, 1] do
        for c in [false, true] do
          unless agrees 1 K a b c do throw (IO.userError s!"1-bit, K = {K}: {a} + {b} + {c}")
  IO.println "1-bit carry-lookahead adder (K = 0, 1) agrees with BitVec.adc on all inputs"

-- the Kogge-Stone prefix specification gives every carry, for widths up to 6
#eval do
  let mut count := 0
  for n in [1, 2, 3, 4, 5, 6] do
    for a in List.range (2 ^ n) do
      for b in List.range (2 ^ n) do
        for c in [false, true] do
          let x := BitVec.ofNat n a
          let y := BitVec.ofNat n b
          for i in List.range n do
            let g := gpSpec x y (claLevels n) i
            unless BitVec.carry (i + 1) x y c == (g.1 || (g.2 && c)) do
              throw (IO.userError s!"width {n}: carry {i + 1} of {a} + {b} + {c}")
          count := count + 1
  IO.println s!"gpSpec after claLevels n levels gives every carry on all {count} inputs, n ≤ 6"

#eval do
  for (n, K) in [(1, 0), (1, 1), (2, 1), (4, 2), (8, 3), (16, 4)] do
    unless (carryLookaheadAdder n K).size == 5 * n + 3 * n * K do
      throw (IO.userError s!"size of the ({n}, {K}) adder")
  unless (rippleCarryAdder 2).depth == 5 && (rippleCarryAdder 3).depth == 7 do
    throw (IO.userError "ripple-carry depth")
  IO.println "sizes match 5 n + 3 n K for (n, K) up to (16, 4); \
    ripple-carry depths 5 and 7 for 2 and 3 bits"

/-! Closed checks -/

example (x y : BitVec 64) (c : Bool) :
    (carryLookaheadAdder 64 (claLevels 64)).eval arithInterpretation (rcaInput x y c)
        ⟨64, by omega⟩ = (BitVec.adc x y c).1 :=
  carryLookaheadAdder_carry x y c (le_two_pow_claLevels 64)

example : (carryLookaheadAdder 64 (claLevels 64)).depth = 2 * Nat.log2 64 + 5 :=
  carryLookaheadAdder_depth_claLevels (by decide)

#print axioms carryLookaheadAdder_sum
#print axioms carryLookaheadAdder_carry
#print axioms carryLookaheadAdder_size
#print axioms carryLookaheadAdder_depth
#print axioms carryLookaheadAdder_depth_claLevels
#print axioms rippleCarryAdder_depth
#print axioms Program.depths_eq_eval

end Cslib.Circuits
