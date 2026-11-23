/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.AncestralReconstruction
public meta import CSLibExt.Bioinformatics.Phylogenetics.AncestralReconstruction
public meta import CSLibExt.Bioinformatics.Phylogenetics.FelsensteinPruning
public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Ring.Int

/-!
# Joint ancestral reconstruction tests

* Closed checks over `S = Bool`, `R = ℕ`: `maxPrune` on two- and three-leaf trees equals the
  maximum over all labelings (by `decide`), and the theorems instantiate on these trees with
  their nonnegativity hypotheses discharged (non-vacuity witness for `NonnegWeights`).
* Executed fixtures: on 40 pseudo-random trees over `ℚ` with nonnegative weights, `maxPrune`
  agrees with the brute-force maximum over all labelings.
* Boundary: over `ℤ` with a negative transition weight, some labeling has weight larger than
  `maxPrune`, so the nonnegativity hypotheses of `weight_le_maxPrune` cannot be dropped.
-/

namespace Cslib.Bioinformatics.Phylogenetics.AncestralReconstruction

open Cslib.Bioinformatics.Phylogenetics.FelsensteinPruning Finset

/-! ## Closed checks over `Bool` and `ℕ` -/

/-- Transition weights on `Bool`: `3` to stay, `1` to switch. -/
def P₁ : Bool → Bool → ℕ := fun a b => if a = b then 3 else 1

/-- Transition weights on `Bool`: `2` into `true`, `1` into `false`. -/
def P₂ : Bool → Bool → ℕ := fun _ b => if b then 2 else 1

/-- Leaf data: leaf `0` observed `true`, leaf `1` observed `false`, leaf `2` ambiguous. -/
def obs₀ : Fin 3 → Bool → ℕ
  | 0, b => if b then 1 else 0
  | 1, b => if b then 0 else 1
  | 2, _ => 1

/-- The cherry `(0, 1)`. -/
def cherry : Tree (Fin 3) Bool ℕ := .node P₁ (.leaf 0) P₂ (.leaf 1)

/-- The three-leaf tree `((0, 1), 2)`. -/
def tree3 : Tree (Fin 3) Bool ℕ := .node P₂ cherry P₁ (.leaf 2)

example : maxPrune obs₀ cherry true = 3 := by decide
example : maxPrune obs₀ cherry false = 1 := by decide
example : maxPrune obs₀ tree3 true = 18 := by decide

-- `maxPrune` is the maximum over all `16` labelings of the three-leaf tree.
example (s : Bool) : (∀ z, weight obs₀ tree3 s z ≤ maxPrune obs₀ tree3 s) ∧
    ∃ z, weight obs₀ tree3 s z = maxPrune obs₀ tree3 s := by
  cases s <;> decide

/-- Non-vacuity witness: the three-leaf tree has nonnegative weights. -/
theorem tree3_nonneg : NonnegWeights tree3 :=
  ⟨fun _ _ => Nat.zero_le _, fun _ _ => Nat.zero_le _,
    ⟨fun _ _ => Nat.zero_le _, fun _ _ => Nat.zero_le _, trivial, trivial⟩, trivial⟩

example (z : Labeling tree3) (s : Bool) : weight obs₀ tree3 s z ≤ maxPrune obs₀ tree3 s :=
  weight_le_maxPrune obs₀ (fun _ _ => Nat.zero_le _) tree3 tree3_nonneg s z

example (π : Bool → ℕ) (s : Bool) (z : Labeling tree3) :
    π s * weight obs₀ tree3 s z ≤
      π (pupko obs₀ tree3 π).1 * weight obs₀ tree3 (pupko obs₀ tree3 π).1 (pupko obs₀ tree3 π).2 :=
  pupko_isJointML obs₀ (fun _ _ => Nat.zero_le _) tree3 tree3_nonneg π (fun _ => Nat.zero_le _)
    s z

-- The traced labeling attains the maximum.
example (s : Bool) : weight obs₀ tree3 s (traceback obs₀ tree3 s) = maxPrune obs₀ tree3 s :=
  weight_traceback obs₀ tree3 s

/-! ## Executed fixtures over `ℚ` -/

/-- A pseudo-random tree with `k` internal nodes over `Fin n`, with transition weights read
from `w`; leaves are numbered from `i`. -/
def randTree (n : ℕ) (w : Array ℚ) : ℕ → ℕ → Tree ℕ (Fin n) ℚ × ℕ
  | 0, i => (.leaf i, i + 1)
  | k + 1, i =>
    let (l, i) := randTree n w (k / 2) i
    let (r, i) := randTree n w (k - k / 2) i
    (.node (fun a b => w.getD ((7 * i + 3 * a.val + b.val) % w.size) 0) l
      (fun a b => w.getD ((11 * i + 5 * a.val + 2 * b.val + 1) % w.size) 0) r, i)

/-- `maxPrune obs t a` bounds the weight of every labeling and is attained by one. -/
def maxOk {n : ℕ} [Nonempty (Fin n)] (t : Tree ℕ (Fin n) ℚ) (obs : ℕ → Fin n → ℚ) (a : Fin n) :
    Bool :=
  let v := maxPrune obs t a
  ((univ : Finset (Labeling t)).filter fun z => v < weight obs t a z).card == 0 &&
    ((univ : Finset (Labeling t)).filter fun z => weight obs t a z = v).card != 0

#eval do
  let mut s := 17
  for _ in [0:40] do
    s := (s * 1103515245 + 12345) % 2147483648
    let m := s / 7 % 2
    s := (s * 1103515245 + 12345) % 2147483648
    let k := s / 7 % 3 + 1
    let mut ws : Array ℚ := #[]
    for _ in [0:37] do
      s := (s * 1103515245 + 12345) % 2147483648
      ws := ws.push (((s / 11 % 7 : ℕ) : ℚ) / 3)
    let t := (randTree (m + 2) ws k 0).1
    let obs : ℕ → Fin (m + 2) → ℚ := fun l a => ws.getD ((13 * l + a.val + 5) % 37) 0
    for a in List.finRange (m + 2) do
      unless maxOk t obs a do
        throw <| IO.userError s!"maxPrune ≠ brute-force maximum at n={m + 2}, k={k}"
  IO.println "40 random trees: maxPrune = brute-force maximum over labelings"

/-! ## Boundary: negative weights -/

/-- A negative transition weight on `Bool` over `ℤ`: `-1` into `true`, `-2` into `false`. -/
def Pneg : Bool → Bool → ℤ := fun _ b => if b then -1 else -2

/-- The cherry with negative weights on both edges and leaf weights `1`. -/
def cherryNeg : Tree (Fin 2) Bool ℤ := .node Pneg (.leaf 0) Pneg (.leaf 1)

-- The max-product value is `(-1) * (-1) = 1`, but the labeling with both children `false`
-- has weight `(-2) * (-2) = 4`.
example : maxPrune (fun _ _ => (1 : ℤ)) cherryNeg true = 1 := by decide
example : ∃ z : Labeling cherryNeg,
    maxPrune (fun _ _ => (1 : ℤ)) cherryNeg true < weight (fun _ _ => 1) cherryNeg true z :=
  ⟨((false, PUnit.unit), (false, PUnit.unit)), by decide⟩

end Cslib.Bioinformatics.Phylogenetics.AncestralReconstruction
