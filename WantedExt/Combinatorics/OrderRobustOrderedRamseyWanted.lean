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

/-- **Ordered embedding.** Let $<_H$ be a strict total order on $\{0, \dots, n - 1\}$. A map
$f \colon \{0, \dots, n - 1\} \to \{0, \dots, N - 1\}$ is an ordered embedding when it is
injective and $a <_H b$ implies $f(a) < f(b)$ for all $a$ and $b$, where $\{0, \dots, N - 1\}$
carries its natural order.

Source: [AIM-COMBINATORICS-0079] Order-robust ordered Ramsey numbers of regular
graphs (aim-combinatorics-notes.json notes[78], Source item 32,
Section: Ordered Ramsey numbers, Workshop: Graph Ramsey theory,
https://www.overleaf.com/read/mnvcscjjysvg). -/
def IsOrderedEmbedding {n N : Nat} (ordH : MathlibExt.Order.StrictTotalOrder (Fin n))
    (f : Fin n → Fin N) : Prop :=
  Function.Injective f ∧ ∀ a b : Fin n, ordH.lt a b → f a < f b

/-- **Red ordered copy.** Let $H$ be a simple graph on $\{0, \dots, n - 1\}$ with a strict total
order $<_H$ on its vertices, and let $G$ be a simple graph on $\{0, \dots, N - 1\}$, the red
graph. Then $G$ contains a red ordered copy of $(H, <_H)$ when there is an ordered embedding $f$
of $(\{0, \dots, n - 1\}, <_H)$ into $\{0, \dots, N - 1\}$ such that $f(a)$ and $f(b)$ are
adjacent in $G$ whenever $a$ and $b$ are adjacent in $H$. The copy need not be induced.

Source: [AIM-COMBINATORICS-0079] Order-robust ordered Ramsey numbers of regular
graphs (aim-combinatorics-notes.json notes[78], Source item 32,
Section: Ordered Ramsey numbers, Workshop: Graph Ramsey theory,
https://www.overleaf.com/read/mnvcscjjysvg). -/
def HasRedOrderedCopy {n N : Nat} (H : SimpleGraph (Fin n))
    (ordH : MathlibExt.Order.StrictTotalOrder (Fin n)) (G : SimpleGraph (Fin N)) : Prop :=
  ∃ f : Fin n → Fin N, IsOrderedEmbedding ordH f ∧
    ∀ a b : Fin n, H.Adj a b → G.Adj (f a) (f b)

/-- **Blue ordered copy.** Let $H$ be a simple graph on $\{0, \dots, n - 1\}$ with a strict total
order $<_H$ on its vertices, and let $G$ be a simple graph on $\{0, \dots, N - 1\}$, the red
graph. Then $G$ admits a blue ordered copy of $(H, <_H)$ when there is an ordered embedding $f$
of $(\{0, \dots, n - 1\}, <_H)$ into $\{0, \dots, N - 1\}$ such that $f(a)$ and $f(b)$ are not
adjacent in $G$ whenever $a$ and $b$ are adjacent in $H$. Since $f$ is injective, these pairs are
edges of the blue graph, the complement of $G$. The copy need not be induced.

Source: [AIM-COMBINATORICS-0079] Order-robust ordered Ramsey numbers of regular
graphs (aim-combinatorics-notes.json notes[78], Source item 32,
Section: Ordered Ramsey numbers, Workshop: Graph Ramsey theory,
https://www.overleaf.com/read/mnvcscjjysvg). -/
def HasBlueOrderedCopy {n N : Nat} (H : SimpleGraph (Fin n))
    (ordH : MathlibExt.Order.StrictTotalOrder (Fin n)) (G : SimpleGraph (Fin N)) : Prop :=
  ∃ f : Fin n → Fin N, IsOrderedEmbedding ordH f ∧
    ∀ a b : Fin n, H.Adj a b → ¬ G.Adj (f a) (f b)

/-- **Ordered Ramsey property.** Let $H$ be a simple graph on $\{0, \dots, n - 1\}$ with a strict
total order $<_H$ on its vertices. A natural number $N$ has the ordered Ramsey property for
$(H, <_H)$ when every simple graph $G$ on $\{0, \dots, N - 1\}$ contains a red ordered copy of
$(H, <_H)$ or admits a blue ordered copy of $(H, <_H)$. Equivalently, every red/blue colouring of
the edges of the complete graph on $\{0, \dots, N - 1\}$ with its natural order, with red edges
those of $G$, contains a monochromatic ordered copy of $(H, <_H)$.

Source: [AIM-COMBINATORICS-0079] Order-robust ordered Ramsey numbers of regular
graphs (aim-combinatorics-notes.json notes[78], Source item 32,
Section: Ordered Ramsey numbers, Workshop: Graph Ramsey theory,
https://www.overleaf.com/read/mnvcscjjysvg). -/
def OrderedRamseyProp {n : Nat} (H : SimpleGraph (Fin n))
    (ordH : MathlibExt.Order.StrictTotalOrder (Fin n)) (N : Nat) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    HasRedOrderedCopy H ordH G ∨ HasBlueOrderedCopy H ordH G

/-- **Ordered Ramsey number.** For a simple graph $H$ on $\{0, \dots, n - 1\}$ with a strict total
order $<_H$ on its vertices, the ordered Ramsey number $r_<(H, <_H)$ is the least natural number
$N$ with the ordered Ramsey property for $(H, <_H)$, that is, such that every red/blue colouring
of the edges of the complete graph on $\{0, \dots, N - 1\}$ with its natural order contains a
monochromatic ordered copy of $(H, <_H)$. It is $0$ if no such $N$ exists.

Source: [AIM-COMBINATORICS-0079] Order-robust ordered Ramsey numbers of regular
graphs (aim-combinatorics-notes.json notes[78], Source item 32,
Section: Ordered Ramsey numbers, Workshop: Graph Ramsey theory,
https://www.overleaf.com/read/mnvcscjjysvg). -/
noncomputable def orderedRamseyNumber {n : Nat} (H : SimpleGraph (Fin n))
    (ordH : MathlibExt.Order.StrictTotalOrder (Fin n)) : Nat :=
  sInf { N : Nat | OrderedRamseyProp H ordH N }

/-- **Order-robust ordered Ramsey conjecture for 100-regular graphs.** There are a real number
$c > 0$ and a natural number $N_0$ such that for every $n \ge N_0$ there is a $100$-regular simple
graph $H$ on $\{0, \dots, n - 1\}$ such that $r_<(H, <_H) \ge n^{1+c}$ for every strict total
order $<_H$ on its vertices, where $r_<(H, <_H)$ is the ordered Ramsey number of $H$ with the
order $<_H$.

This is the AIM question asking whether such a $c$ exists, stated as a claim.

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
**The order-robust ordered Ramsey conjecture holds.** There are a real number $c > 0$ and a
natural number $N_0$ such that for every $n \ge N_0$ there is a $100$-regular simple graph $H$ on
$\{0, \dots, n - 1\}$ such that $r_<(H, <_H) \ge n^{1+c}$ for every strict total order $<_H$ on
its vertices. Here $r_<(H, <_H)$ is the least $N$ such that every red/blue colouring of the edges
of the complete graph on $\{0, \dots, N - 1\}$ with its natural order contains a monochromatic
copy of $H$ (not necessarily induced) under an injective map sending $<_H$ into the natural
order, and $0$ if there is no such $N$.

Balko, Jelínek and Valtr prove that for every $d \ge 3$ almost every $d$-regular $n$-vertex
graph has ordered Ramsey number at least $n^{3/2-1/d}/(4 \log n \log \log n)$ under every vertex
ordering; for $d = 100$ this exceeds $n^{1+c}$ for any $c < 49/100$ and all large $n$.

Source: M.
Balko, V. Jelínek and P. Valtr, On ordered Ramsey numbers of bounded-degree graphs,
arXiv:1606.05628, https://arxiv.org/abs/1606.05628. Moved from
`OpenConjectures/Combinatorics/OrderRobustOrderedRamsey`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.OrderRobustOrderedRamseyWanted
