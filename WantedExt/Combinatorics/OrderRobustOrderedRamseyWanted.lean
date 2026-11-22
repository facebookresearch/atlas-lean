/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Order-robust ordered Ramsey numbers of regular graphs

`AIM-COMBINATORICS-0079` (AIM Graph Ramsey theory, Ordered Ramsey
numbers, item 32): does there exist `c > 0` such that for every
sufficiently large `n` there is a 100-regular graph `H` on `n`
vertices with `r_<(H) ≥ n^(1+c)` for every ordering of `H`?
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Order.StrictTotalOrder
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.OrderRobustOrderedRamseyWanted

/-- Injective order-preserving embeddings from an ordered `n`-vertex graph into
`Fin N` with its natural order.
Source: [AIM-COMBINATORICS-0079] Order-robust ordered Ramsey numbers of regular
graphs (aim-combinatorics-notes.json notes[78], Source item 32,
Section: Ordered Ramsey numbers, Workshop: Graph Ramsey theory,
https://www.overleaf.com/read/mnvcscjjysvg). -/
def IsOrderedEmbedding {n N : Nat} (ordH : MathlibExt.Order.StrictTotalOrder (Fin n))
    (f : Fin n → Fin N) : Prop :=
  Function.Injective f ∧ ∀ a b : Fin n, ordH.lt a b → f a < f b

/-- Red ordered (not necessarily induced) copies of `H` inside the red graph `G`.
Source: [AIM-COMBINATORICS-0079] Order-robust ordered Ramsey numbers of regular
graphs (aim-combinatorics-notes.json notes[78], Source item 32,
Section: Ordered Ramsey numbers, Workshop: Graph Ramsey theory,
https://www.overleaf.com/read/mnvcscjjysvg). -/
def HasRedOrderedCopy {n N : Nat} (H : SimpleGraph (Fin n))
    (ordH : MathlibExt.Order.StrictTotalOrder (Fin n)) (G : SimpleGraph (Fin N)) : Prop :=
  ∃ f : Fin n → Fin N, IsOrderedEmbedding ordH f ∧
    ∀ a b : Fin n, H.Adj a b → G.Adj (f a) (f b)

/-- Blue ordered (not necessarily induced) copies of `H`, where blue is the
complement of the red graph `G` off the diagonal.
Source: [AIM-COMBINATORICS-0079] Order-robust ordered Ramsey numbers of regular
graphs (aim-combinatorics-notes.json notes[78], Source item 32,
Section: Ordered Ramsey numbers, Workshop: Graph Ramsey theory,
https://www.overleaf.com/read/mnvcscjjysvg). -/
def HasBlueOrderedCopy {n N : Nat} (H : SimpleGraph (Fin n))
    (ordH : MathlibExt.Order.StrictTotalOrder (Fin n)) (G : SimpleGraph (Fin N)) : Prop :=
  ∃ f : Fin n → Fin N, IsOrderedEmbedding ordH f ∧
    ∀ a b : Fin n, H.Adj a b → ¬ G.Adj (f a) (f b)

/-- Ordered Ramsey property at `N`: every red/blue coloring of the complete
ordered graph on `N` vertices contains a monochromatic ordered copy of `H`.
Source: [AIM-COMBINATORICS-0079] Order-robust ordered Ramsey numbers of regular
graphs (aim-combinatorics-notes.json notes[78], Source item 32,
Section: Ordered Ramsey numbers, Workshop: Graph Ramsey theory,
https://www.overleaf.com/read/mnvcscjjysvg). -/
def OrderedRamseyProp {n : Nat} (H : SimpleGraph (Fin n))
    (ordH : MathlibExt.Order.StrictTotalOrder (Fin n)) (N : Nat) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    HasRedOrderedCopy H ordH G ∨ HasBlueOrderedCopy H ordH G

/-- Ordered Ramsey number `r_<(H)` as the infimum of `N` satisfying the ordered
Ramsey property.
Source: [AIM-COMBINATORICS-0079] Order-robust ordered Ramsey numbers of regular
graphs (aim-combinatorics-notes.json notes[78], Source item 32,
Section: Ordered Ramsey numbers, Workshop: Graph Ramsey theory,
https://www.overleaf.com/read/mnvcscjjysvg). -/
noncomputable def orderedRamseyNumber {n : Nat} (H : SimpleGraph (Fin n))
    (ordH : MathlibExt.Order.StrictTotalOrder (Fin n)) : Nat :=
  sInf { N : Nat | OrderedRamseyProp H ordH N }

/-- Does there exist `c > 0` such that for every sufficiently large `n` there
exists a 100-regular graph `H` on `n` vertices with `r_<(H) ≥ n ^ (1 + c)` for
every ordering of `H`?
Source: [AIM-COMBINATORICS-0079] Order-robust ordered Ramsey numbers of regular
graphs (aim-combinatorics-notes.json notes[78], Source item 32,
Section: Ordered Ramsey numbers, Workshop: Graph Ramsey theory,
https://www.overleaf.com/read/mnvcscjjysvg). -/
def conjecture : Prop :=
  ∃ c : Real, 0 < c ∧ ∃ N0 : Nat, ∀ n : Nat, N0 ≤ n →
    ∃ H : SimpleGraph (Fin n), letI : H.LocallyFinite := fun _ ↦ Fintype.ofFinite _;
      H.IsRegularOfDegree 100 ∧
      ∀ ordH : MathlibExt.Order.StrictTotalOrder (Fin n),
        Real.rpow (n : Real) ((1 : Real) + c) ≤
          (orderedRamseyNumber H ordH : Real)

/--
Resolved true: Resolved true: Balko, Jelínek and Valtr (On ordered Ramsey numbers of
bounded-degree graphs, arXiv:1606.05628) prove that for every d >= 3 almost every d-regular
n-vertex graph has ordered Ramsey number at least n^{3/2-1/d}/(4 log n log log n) under every
vertex ordering; for d = 100 this exceeds n^{1+c} for any c < 49/100 and all large n. Source: M.
Balko, V. Jelínek and P. Valtr, On ordered Ramsey numbers of bounded-degree graphs,
arXiv:1606.05628, https://arxiv.org/abs/1606.05628. Moved from
`OpenConjectures/Combinatorics/OrderRobustOrderedRamsey`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.OrderRobustOrderedRamseyWanted
