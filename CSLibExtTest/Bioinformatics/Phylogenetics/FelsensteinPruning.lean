/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.FelsensteinPruning
public meta import CSLibExt.Bioinformatics.Phylogenetics.FelsensteinPruning
public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Felsenstein pruning tests

Closed checks: on two- and three-leaf trees over `S = Bool` and `R = ℕ`, `prune` equals the
explicit sum over the internal states (by `decide`) and equals the brute-force `bruteLik`; the
number of labelings is `|S| ^ (2 · #internal nodes)`. Executed fixtures: on 40 pseudo-random
trees over `ℚ` (2 to 3 states, 1 to 2 internal nodes, random weights), the tabulated
`pruneTab` agrees with the brute-force sum over all labelings, and the alignment likelihood of
two independent sites (summed over pairs of per-site root states and labelings) equals the
product of the site likelihoods. Each run throws on a
disagreement.
-/

namespace Cslib.Bioinformatics.Phylogenetics.FelsensteinPruning

/-! ## Closed checks over `Bool` and `ℕ` -/

/-- Transition weights on `Bool`: `2` to stay, `1` to switch. -/
def P₁ : Bool → Bool → ℕ := fun a b => if a = b then 2 else 1

/-- Transition weights on `Bool`: `3` into `true`, `1` into `false`. -/
def P₂ : Bool → Bool → ℕ := fun _ b => if b then 3 else 1

/-- Leaf data: leaf `0` observed `true`, leaf `1` observed `false`, leaf `2` ambiguous. -/
def obs₀ : Fin 3 → Bool → ℕ
  | 0, b => if b then 1 else 0
  | 1, b => if b then 0 else 1
  | 2, _ => 1

/-- The cherry `(0, 1)`. -/
def cherry : Tree (Fin 3) Bool ℕ := .node P₁ (.leaf 0) P₂ (.leaf 1)

/-- The three-leaf tree `((0, 1), 2)`. -/
def tree3 : Tree (Fin 3) Bool ℕ := .node P₂ cherry P₁ (.leaf 2)

-- Two leaves: `prune` is the explicit sum over the two child states.
example (s : Bool) :
    prune obs₀ cherry s = ∑ a, ∑ b, P₁ s a * obs₀ 0 a * (P₂ s b * obs₀ 1 b) := by
  cases s <;> decide

example : prune obs₀ cherry true = 2 := by decide
example : prune obs₀ cherry false = 1 := by decide

-- Three leaves: the explicit sum over the cherry's root state and all leaf states.
example (s : Bool) :
    prune obs₀ tree3 s =
      ∑ c, ∑ a, ∑ b, ∑ d, P₂ s c * (P₁ c a * obs₀ 0 a * (P₂ c b * obs₀ 1 b)) *
        (P₁ s d * obs₀ 2 d) := by
  cases s <;> decide

example : prune obs₀ tree3 true = (3 * 2 + 1 * 1) * (2 + 1) := by decide

-- The brute-force sum over labelings agrees.
example : bruteLik obs₀ tree3 true = 21 := by
  rw [← prune_eq_bruteLik]; decide

example : bruteLik obs₀ tree3 false = 21 := by decide

example : likelihood obs₀ tree3 (fun _ => 1) = 42 := by
  rw [likelihood_eq_sum_prune]; decide

-- Labelings: `2 ^ (2 · 2) = 16` for the three-leaf tree; one for a leaf.
example : Fintype.card (Labeling tree3) = 16 := by
  rw [card_labeling]; rfl

example : Fintype.card (Labeling (.leaf 0 : Tree (Fin 3) Bool ℕ)) = 1 := by
  rw [card_labeling]; rfl

-- The tabulated algorithm on `Fin 2`.
example : (pruneTab (fun (_ : Fin 3) (_ : Fin 2) => (1 : ℕ))
    (.node (fun _ _ => 1) (.leaf 0) (fun _ _ => 1) (.leaf 1)))[(0 : Fin 2)] = 4 := by
  decide

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

/-- The two-site alignment likelihood, by brute force over pairs of per-site root states and
labelings, equals the product of the two site likelihoods. -/
def sitesOk {n : ℕ} (t : Tree ℕ (Fin n) ℚ) (obs obs' : ℕ → Fin n → ℚ) (π : Fin n → ℚ) : Bool :=
  (∑ p : (Fin n × Labeling t) × (Fin n × Labeling t),
      π p.1.1 * weight obs t p.1.1 p.1.2 * (π p.2.1 * weight obs' t p.2.1 p.2.2)) ==
    likelihood obs t π * likelihood obs' t π

#eval do
  let mut s := 41
  for _ in [0:40] do
    s := (s * 1103515245 + 12345) % 2147483648
    let n := s / 7 % 2 + 2
    s := (s * 1103515245 + 12345) % 2147483648
    let k := s / 7 % 2 + 1
    let mut ws : Array ℚ := #[]
    for _ in [0:37] do
      s := (s * 1103515245 + 12345) % 2147483648
      ws := ws.push ((s / 11 % 5 : ℕ) : ℚ)
    let t := (randTree n ws k 0).1
    let obs : ℕ → Fin n → ℚ := fun l a => ws.getD ((13 * l + a.val + 5) % 37) 0
    let obs' : ℕ → Fin n → ℚ := fun l a => ws.getD ((17 * l + 2 * a.val + 9) % 37) 0
    for a in List.finRange n do
      if (pruneTab obs t)[a] ≠ bruteLik obs t a then
        throw <| IO.userError s!"pruneTab ≠ bruteLik at n={n}, k={k}"
    let π : Fin n → ℚ := fun a => ws.getD a.val 0
    unless sitesOk t obs obs' π do
      throw <| IO.userError s!"independent sites fail at n={n}, k={k}"
  IO.println "40 random trees: pruneTab = brute force; two sites = product of site likelihoods"

/-! ## Instantiated theorems -/

example (t : Tree (Fin 3) Bool ℕ) (s : Bool) : prune obs₀ t s = bruteLik obs₀ t s :=
  prune_eq_bruteLik obs₀ t s

example (obs : Fin 2 → ℕ → Fin 2 → ℚ) (t : Tree ℕ (Fin 2) ℚ) (π : Fin 2 → ℚ) :
    ∑ σ : Fin 2 → Fin 2 × Labeling t, ∏ k, π (σ k).1 * weight (obs k) t (σ k).1 (σ k).2 =
      likelihood (obs 0) t π * likelihood (obs 1) t π := by
  rw [sum_prod_siteWeight_eq_prod_likelihood, Fin.prod_univ_two]

#print axioms prune_eq_bruteLik
#print axioms pruneTab_get
#print axioms sum_prod_siteWeight_eq_prod_likelihood

end Cslib.Bioinformatics.Phylogenetics.FelsensteinPruning
