/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PERIODIC SQUARE-TILING WITH BOUNDED PERIOD: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GP13] SQUARE-TILING, comment
(p. 257: "Variant in which we ask if T can be used to tile the entire plane (Z×Z)
'periodically' with period less than N is also NP-complete"), credited there to
[Garey, Johnson, and Papadimitriou, 1977], listed in the book's bibliography as unpublished
results.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SquareTilingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PeriodicSquareTiling

open MetaMathlibExt.Complexity.NPComplete.SquareTiling (SquareTilingInstance)

/-- A tiling of the plane with period `p` in both directions, for some `0 < p < N`: every
position `(x, y) ∈ ℤ × ℤ` gets a tile of `T`, horizontally adjacent tiles agree on the shared
right/left color, vertically adjacent tiles agree on the shared bottom/top color, and
`f (x + p) y = f x y = f x (y + p)`. -/
def PeriodicSquareTilingFeasible (i : SquareTilingInstance) : Prop :=
  ∃ p : ℕ, 0 < p ∧ p < i.2.2 ∧ ∃ f : ℤ → ℤ → ℕ × ℕ × ℕ × ℕ,
    (∀ x y, f x y ∈ i.2.1) ∧
    (∀ x y, (f x y).2.1 = (f (x + 1) y).2.2.2) ∧
    (∀ x y, (f x y).2.2.1 = (f x (y + 1)).1) ∧
    (∀ x y, f (x + p) y = f x y ∧ f x (y + p) = f x y)

open Classical in
/-- PERIODIC SQUARE-TILING WITH BOUNDED PERIOD as a decision problem over bitstrings. -/
noncomputable def periodicSquareTilingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SquareTilingInstance) x with
  | some i => decide (SquareTiling.WellFormed i ∧ PeriodicSquareTilingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PeriodicSquareTiling
