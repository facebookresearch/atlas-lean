/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Perceptron
public meta import CSLibExt.MachineLearning.Perceptron
public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fin.VecNotation
public meta import Mathlib.Data.Fin.VecNotation

/-!
# Perceptron tests

Executed fixtures, over `ℚ` with a bias coordinate: for separable data with a known separator
`u`, each run computes the margin `γ` and radius `R²`, runs the perceptron from `0` over several
passes concatenated into one sequence, and checks Novikoff's bound
`mistakes * γ ^ 2 ≤ (u ⬝ᵥ u) * R ^ 2`; it then checks that `train` with the first pass count past
the bound returns weights classifying every example strictly correctly. It throws otherwise.
Fixtures: logical AND, a line in the plane, and 40 pseudo-random separable data sets.
XOR is not separable: `train` gives up after 30 passes. Closed checks instantiate the theorems.
-/

set_option autoImplicit false

namespace Cslib.MachineLearning.Perceptron

open Matrix

private abbrev Pt := Fin 3 → ℚ

private meta def pt (a b : ℚ) : Pt := ![1, a, b]

private meta def check (label : String) (u : Pt) (xs : List (Pt × Bool)) (passes : ℕ := 5)
    (quiet : Bool := false) : IO Unit := do
  let margins := xs.map fun e => (sign e.2 : ℚ) * (u ⬝ᵥ e.1)
  let γ := margins.foldl min (margins.headD 0)
  let R2 := (xs.map fun e => e.1 ⬝ᵥ e.1).foldl max 0
  unless 0 < γ do throw (IO.userError s!"{label}: u does not separate the data")
  let k := (run 0 0 (List.replicate passes xs).flatten).2
  unless (k : ℚ) * γ ^ 2 ≤ (u ⬝ᵥ u) * R2 do
    throw (IO.userError s!"{label}: {k} mistakes, bound {(u ⬝ᵥ u) * R2 / γ ^ 2}")
  let n := ((u ⬝ᵥ u) * R2 / γ ^ 2).floor.toNat + 1
  match train xs n 0 with
  | none => throw (IO.userError s!"{label}: train did not converge in {n} passes")
  | some v =>
    unless xs.all fun e => 0 < (sign e.2 : ℚ) * (v ⬝ᵥ e.1) do
      throw (IO.userError s!"{label}: returned weights misclassify")
    unless quiet do
      IO.println s!"{label}: {k} mistakes over {passes} passes ≤ (u ⬝ᵥ u) R² / γ² = \
        {(u ⬝ᵥ u) * R2 / γ ^ 2}; train converged within {n} passes, w = {(List.finRange 3).map v}"

#eval check "AND" (pt 2 2 - ![4, 0, 0])
  [(pt 0 0, false), (pt 1 0, false), (pt 0 1, false), (pt 1 1, true)]
#eval check "the line b = a + 1/2" (![-1, -2, 2])
  [(pt 0 2, true), (pt 1 3, true), (pt 2 1, false), (pt (-1) 1, true), (pt 3 2, false),
    (pt 0 (-1), false), (pt 4 6, true)]

-- XOR is not linearly separable: no pass is mistake-free.
#eval do
  let xs : List (Pt × Bool) := [(pt 0 0, false), (pt 1 0, true), (pt 0 1, true), (pt 1 1, false)]
  unless (train xs 30 0).isNone do throw (IO.userError "XOR: train converged")
  IO.println "XOR: train gives up after 30 passes"

/-- Pseudo-random separable data: integer points in `[-5, 5]²` labelled by `u`, keeping only
points with `|u ⬝ᵥ x| ≥ 1`. -/
private meta def randData (seed : ℕ) : Pt × List (Pt × Bool) := Id.run do
  let mut s := seed
  let next (s : ℕ) : ℕ := (s * 1103515245 + 12345) % 2147483648
  s := next s
  let u : Pt :=
    ![((s / 3 % 11 : ℕ) : ℚ) - 5, ((s / 37 % 7 : ℕ) : ℚ) - 3, ((s / 101 % 7 : ℕ) : ℚ) - 3]
  let mut xs : List (Pt × Bool) := []
  for _ in [0:12] do
    s := next s
    let x := pt (((s / 7 % 11 : ℕ) : ℚ) - 5) (((s / 131 % 11 : ℕ) : ℚ) - 5)
    let m := u ⬝ᵥ x
    if 1 ≤ m then xs := xs ++ [(x, true)]
    else if m ≤ -1 then xs := xs ++ [(x, false)]
  return (u, xs)

#eval do
  let mut sets := 0
  for i in [0:40] do
    let (u, xs) := randData (i * 7919 + 3)
    if xs.isEmpty then continue
    check s!"random {i}" u xs (passes := 8) (quiet := true)
    sets := sets + 1
  IO.println s!"{sets} pseudo-random separable data sets: bound holds and train converges"

/-! Closed checks -/

example (u : Pt) (γ R : ℚ) (xs : List (Pt × Bool))
    (hsep : ∀ e ∈ xs, γ ≤ sign e.2 * (u ⬝ᵥ e.1)) (hR : ∀ e ∈ xs, e.1 ⬝ᵥ e.1 ≤ R ^ 2)
    (hγ : 0 < γ) : ((run 0 0 xs).2 : ℚ) ≤ (u ⬝ᵥ u) * R ^ 2 / γ ^ 2 :=
  mistakes_le_div xs hsep hR hγ

#print axioms mistakes_mul_sq_le
#print axioms mistakes_le_div
#print axioms train_converges
#print axioms train_classifies

end Cslib.MachineLearning.Perceptron
