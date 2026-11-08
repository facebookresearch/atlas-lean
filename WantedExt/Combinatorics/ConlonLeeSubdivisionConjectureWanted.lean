/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Source record `OWR-16931-006`
# The Conlon–Lee conjecture on extremal numbers of subdivisions

Combinatorics, Probability and Computing (2020), Oberwolfach Reports, DOI 10.4171/owr/2019/19, pp.
1113--1189.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.ConlonLeeSubdivisionConjectureWanted

/-- The `(k - 1)`-subdivision `H^{k-1}` of a graph `H` on `Fin m`: every edge `ij` (`i < j`)
is replaced by a path `i — (ij, 0) — ⋯ — (ij, k - 2) — j` of length `k` through `k - 1` new
vertices. -/
def subdivision {m : ℕ} (H : SimpleGraph (Fin m)) (k : ℕ) :
    SimpleGraph (Fin m ⊕ ({p : Fin m × Fin m // p.1 < p.2 ∧ H.Adj p.1 p.2} × Fin (k - 1))) :=
  SimpleGraph.fromRel fun u v => match u, v with
    | .inl i, .inr (e, t) => e.1.1 = i ∧ (t : ℕ) = 0
    | .inr (e, t), .inr (e', t') => e = e' ∧ (t' : ℕ) = t + 1
    | .inr (e, t), .inl j => e.1.2 = j ∧ (t : ℕ) = k - 2
    | _, _ => False

/-- `G` contains a copy of `F` (not necessarily induced). -/
def ContainsCopy {V W : Type} (F : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∃ f : V ↪ W, ∀ u v, F.Adj u v → G.Adj (f u) (f v)

open Classical in
/-- The extremal number `ex(n, F)`: the maximum number of edges of an `F`-free graph on `n`
vertices. -/
noncomputable def ex {V : Type} (n : ℕ) (F : SimpleGraph V) : ℕ :=
  sSup {e | ∃ G : SimpleGraph (Fin n), ¬ ContainsCopy F G ∧ G.edgeFinset.card = e}

/-- The Conlon–Lee conjecture: for every even `k ≥ 2` and every graph `H` there is `δ > 0` with
`ex(n, H^{k-1}) = O(n^{1 + 1/k - δ})`. -/
def conjecture : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 2 ≤ k → Even k → ∃ δ > (0 : ℝ), ∃ C : ℝ, ∀ n : ℕ,
    (ex n (subdivision H k) : ℝ) ≤ C * (n : ℝ) ^ (1 + 1 / (k : ℝ) - δ)

-- Carried source audit `OWR-16931-006` (see the Moved/ record).

/--
Resolved true: Resolved (true): for every graph H and even k ≥ 2 there is δ > 0 with ex(n,
H^{k−1}) = O(n^{1+1/k−δ}) (Janzer, Bull. London Math. Soc. 53 (2021) 108–118, Theorem 1.7;
arXiv:1905.08001). Source: O. Janzer, The extremal number of longer subdivisions, Bull. London
Math. Soc. 53 (2021) 108-118, arXiv:1905.08001, https://doi.org/10.1112/blms.12404. Moved from
`OpenConjectures/Combinatorics/ConlonLeeSubdivisionConjecture`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ConlonLeeSubdivisionConjectureWanted
