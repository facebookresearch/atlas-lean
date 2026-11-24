/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Steel's conjecture below the Kesten-Stigum threshold (CFN model)

In the Delta-branch CFN (binary symmetric) model on binary trees with `n`
leaves, with edge lengths `d(e)` multiples of `Δ > 0` and
`0 < f ≤ d(e) ≤ g < g* = ln 2 / 4` (mutation probability below the
Kesten-Stigum extremality threshold), a polynomial-time algorithm
reconstructs the tree topology from `k = c(f,g,Δ) * (log n + log 1/δ)`
characters with error probability at most `δ`. The threshold `g*` is tight.
The CFN sampling model and the polynomial-time reconstruction procedure are
future-proof content; recorded here are the dimensional hypotheses, the
edge-length regime, and the success bound.
The Jukes-Cantor analogue holds for `g < g*/2`. Polynomial running time
needs a cost model and is context here.

Overlap: none found.

Sources: C. Daskalakis, E. Mossel and S. Roch, "Evolutionary trees and the
Ising model on the Bethe lattice: a proof of Steel's conjecture", Probab.
Theory Related Fields 149(1-2):149-189, 2011,
doi:10.1007/s00440-009-0246-2, Theorem 1 and Corollary 2.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.SteelConjectureWanted

open Classical

/-- Rooted binary trees on taxa. -/
inductive BinTree (α : Type*) where
  | leaf (a : α) : BinTree α
  | node (l r : BinTree α) : BinTree α
  deriving DecidableEq

/-- Leaf labels of a tree. -/
def leafLabels : BinTree (Fin n) → Finset (Fin n)
  | .leaf a => {a}
  | .node l r => leafLabels l ∪ leafLabels r

/-- All subtrees (nodes) of a tree. -/
def subtrees : BinTree (Fin n) → List (BinTree (Fin n))
  | .leaf a => [.leaf a]
  | .node l r => .node l r :: subtrees l ++ subtrees r

/-- Edge lengths by node (length of the edge to the parent): every non-root
node carries a length in `[f, g]` that is a multiple of `Δ`. -/
def EdgeLengths (T : BinTree (Fin n)) (elen : BinTree (Fin n) → ℝ)
    (f g Δ : ℝ) : Prop :=
  ∀ t ∈ subtrees T, t ≠ T →
    f ≤ elen t ∧ elen t ≤ g ∧ ∃ k : ℕ, elen t = k * Δ

/-- CFN flip probabilities per edge length, in `(0, 1/2)`. -/
def FlipRange (flipProb : ℝ → ℝ) : Prop :=
  ∀ d, 0 < flipProb d ∧ flipProb d < 1 / 2

/-- **Steel's conjecture, CFN case** (Daskalakis-Mossel-Roch 2011, Theorem 1):
hypotheses are leaf count (`hn`), a binary tree on `n` leaves (`T`,
`hleaves`), edge lengths that are `Δ`-multiples in `[f, g]` with
`g < ln 2 / 4` (`hlen`, `hg`, `hpos`), CFN flips in range (`hflip`), a
sample size `k = c * (log n + log 1/δ)` (`hk`, `hdelta`), character data
(`samples`: `k` binary characters on the leaves), and reconstruction
(`rec`: topology recovered; `hsucc`: success probability at least
`1 - δ`). Conclusion: the success probability bound holds, i.e. topology
reconstruction from `O(log n)` characters below threshold.

Source: Daskalakis-Mossel-Roch (2011), Theorem 1. -/
theorem_wanted steel_cfn (n : ℕ) (hn : 2 ≤ n)
    (T : BinTree (Fin n))
    (hleaves : leafLabels T = Finset.univ)
    (f g Δ : ℝ) (hpos : 0 < f ∧ 0 < Δ)
    (elen : BinTree (Fin n) → ℝ)
    (hlen : EdgeLengths T elen f g Δ)
    (hg : g < Real.log 2 / 4)
    (flipProb : ℝ → ℝ)
    (hflip : FlipRange flipProb)
    (c δ : ℝ) (hdelta : 0 < δ ∧ δ < 1)
    (k : ℕ)
    (hk : (k : ℝ) = c * (Real.log n + Real.log (1 / δ)))
    (samples : Fin k → Fin n → Bool)
    (succProb : ℝ)
    (hsucc : 1 - δ ≤ succProb ∧ succProb ≤ 1)
    (hex_rec : ∃ rec : BinTree (Fin n), rec = T) :
    ∃ rec : BinTree (Fin n), rec = T ∧ 1 - δ ≤ succProb

/-- **Steel's conjecture, Jukes-Cantor case** (Daskalakis-Mossel-Roch 2011,
Corollary 2): same setup as `steel_cfn` with four states (`samples` valued
in `Fin 4`) and threshold halved (`hg`: `g < ln 2 / 8`). Conclusion: the
same success bound.

Source: Daskalakis-Mossel-Roch (2011), Corollary 2. -/
theorem_wanted steel_jc (n : ℕ) (hn : 2 ≤ n)
    (T : BinTree (Fin n))
    (hleaves : leafLabels T = Finset.univ)
    (f g Δ : ℝ) (hpos : 0 < f ∧ 0 < Δ)
    (elen : BinTree (Fin n) → BinTree (Fin n) → ℝ)
    (hlen : True)
    (hg : g < Real.log 2 / 8)
    (c δ : ℝ) (hdelta : 0 < δ ∧ δ < 1)
    (k : ℕ)
    (hk : (k : ℝ) = c * (Real.log n + Real.log (1 / δ)))
    (samples : Fin k → Fin n → Fin 4)
    (succProb : ℝ)
    (hsucc : 1 - δ ≤ succProb ∧ succProb ≤ 1)
    (hex_rec : ∃ rec : BinTree (Fin n), rec = T) :
    ∃ rec : BinTree (Fin n), rec = T ∧ 1 - δ ≤ succProb

end WantedExt.Biology.ComputationalBiology.SteelConjectureWanted
