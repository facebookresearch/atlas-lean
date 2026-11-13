/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Every extremal problem has a finitely forcible optimum (Oberwolfach Reports 11/2010)

Oberwolfach workshop Graph Theory (2010), L. Lovász (joint with B. Szegedy), Extremal graphs and
graph limits: 'One conjecture says that every such extremal problem has an extremal family whose
limit is finitely forcible.'
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Combinatorics.FinitelyForcibleOptimumOWR4212Problem011Wanted

/-!
Source: L. Lovász (joint work with B. Szegedy), Extremal graphs and graph limits, in Graph Theory,
Oberwolfach Reports 7 (2010), no. 11, pp. 554-555, question 1, DOI 10.4171/OWR/2010/11. UnsolvedMath
record UM-30001430 (`OWR-4212-011`), dataset ulamai/UnsolvedMath v1.8.0.

The conjecture is stated as Grzesik, Kráľ and Lovász state it (their Conjecture 1, attributed to
Lovász and described as saying that every extremal problem has a finitely forcible optimum) and
treat it, in the language of graphons. A graphon is a jointly measurable symmetric `W : ℝ → ℝ → ℝ`
with values in `[0, 1]` (only `[0, 1]²` matters); `d(H, W)` is the probability that the `W`-random
graph on `|H|` vertices is isomorphic to `H` (GKL Section 2), computed as the sum of the labelled
densities `τ(G, W)` over the graphs `G` on `Fin k` isomorphic to `H`; weak isomorphism and finite
forcibility are as in GKL Section 2. The source's further question whether extremal graphs can be
completely characterized is open-ended and not formalized.
-/

open MeasureTheory

/-- **Graphon.** A graphon is a function $W$ of two real variables that is jointly measurable
(measurable as a function on $\mathbb{R}^2$), symmetric ($W(x, y) = W(y, x)$ for all real $x, y$)
and takes values in $[0, 1]$ at every point of $\mathbb{R}^2$.

Only the values of $W$ on $[0, 1]^2$ enter the densities. -/
def IsGraphon (W : ℝ → ℝ → ℝ) : Prop :=
  Measurable (Function.uncurry W) ∧ (∀ x y, W x y = W y x) ∧ ∀ x y, W x y ∈ Set.Icc (0 : ℝ) 1

open Classical in
/-- **Labelled density.** For a graph $G$ on the vertex set $\{0, \dots, k-1\}$ and a function $W$
of two real variables, the labelled density of $G$ in $W$ is
$$\tau(G, W) = \int_{[0,1]^k} \prod_{i < j} w_{ij}(x) \, dx,$$
where the integral is with respect to Lebesgue measure (and is taken to be $0$ if the integrand is
not integrable), the product runs over the pairs $i < j$ of vertices, and $w_{ij}(x) = W(x_i, x_j)$
if $i$ and $j$ are adjacent in $G$ and $w_{ij}(x) = 1 - W(x_i, x_j)$ otherwise.

When $W$ is a graphon, $\tau(G, W)$ is the probability that the $W$-random graph on
$\{0, \dots, k-1\}$ (independent uniform points $x_i \in [0, 1]$, each pair $\{i, j\}$ joined
independently with probability $W(x_i, x_j)$) equals $G$. -/
noncomputable def labelledDensity {k : ℕ} (G : SimpleGraph (Fin k)) (W : ℝ → ℝ → ℝ) : ℝ :=
  ∫ x in Set.univ.pi fun _ : Fin k => Set.Icc (0 : ℝ) 1,
    ∏ i : Fin k, ∏ j : Fin k,
      if i < j then (if G.Adj i j then W (x i) (x j) else 1 - W (x i) (x j)) else 1

/-- **Density of a graph in a graphon.** For a graph $H$ on the vertex set $\{0, \dots, k-1\}$ and
a function $W$ of two real variables, the density $d(H, W)$ is the sum of the labelled densities
$\tau(G, W)$ over all graphs $G$ on $\{0, \dots, k-1\}$ that are isomorphic to $H$.

When $W$ is a graphon, $d(H, W)$ is the probability that the $W$-random graph on
$\{0, \dots, k-1\}$ is isomorphic to $H$. -/
noncomputable def density {k : ℕ} (H : SimpleGraph (Fin k)) (W : ℝ → ℝ → ℝ) : ℝ :=
  ∑ᶠ (G : SimpleGraph (Fin k)) (_ : Nonempty (G ≃g H)), labelledDensity G W

/-- **Weak isomorphism.** Two functions $W_1$ and $W_2$ of two real variables are weakly isomorphic
if $d(H, W_1) = d(H, W_2)$ for every natural number $k$ and every graph $H$ on the vertex set
$\{0, \dots, k-1\}$, where $d(H, W)$ is the density of $H$ in $W$.

The notion is meant for graphons, but no graphon condition is imposed on $W_1$ and $W_2$. -/
def WeaklyIsomorphic (W₁ W₂ : ℝ → ℝ → ℝ) : Prop :=
  ∀ (k : ℕ) (H : SimpleGraph (Fin k)), density H W₁ = density H W₂

/-- **Finitely forcible graphon.** A function $W$ of two real variables is finitely forcible if
there are finitely many graphs $H_1, \dots, H_\ell$ such that every graphon $W'$ with
$d(H_i, W') = d(H_i, W)$ for all $i$ is weakly isomorphic to $W$. -/
def IsFinitelyForcible (W : ℝ → ℝ → ℝ) : Prop :=
  ∃ (ℓ : ℕ) (H : Fin ℓ → (k : ℕ) × SimpleGraph (Fin k)), ∀ W', IsGraphon W' →
    (∀ i, density (H i).2 W' = density (H i).2 W) → WeaklyIsomorphic W W'

/-- **Lovász's finitely forcible optimum conjecture.** The proposition that for all graphs
$H_1, \dots, H_\ell$ and reals $d_1, \dots, d_\ell$, if some graphon $W$ satisfies
$d(H_i, W) = d_i$ for every $i$, then some finitely forcible graphon $W_0$ satisfies
$d(H_i, W_0) = d_i$ for every $i$.

This is Lovász's conjecture that every extremal problem has a finitely forcible optimum
(Oberwolfach Report 11/2010, p. 554), in the form of Grzesik, Kráľ and Lovász, Conjecture 1. -/
def finitelyForcibleOptimum : Prop :=
  ∀ (ℓ : ℕ) (H : Fin ℓ → (k : ℕ) × SimpleGraph (Fin k)) (d : Fin ℓ → ℝ),
    (∃ W, IsGraphon W ∧ ∀ i, density (H i).2 W = d i) →
      ∃ W, IsGraphon W ∧ IsFinitelyForcible W ∧ ∀ i, density (H i).2 W = d i

/--
**Lovász's finitely forcible optimum conjecture is false.** There are graphs $H_1, \dots, H_\ell$
and reals $d_1, \dots, d_\ell$ such that some graphon $W$ satisfies $d(H_i, W) = d_i$ for every $i$,
but no finitely forcible graphon $W_0$ satisfies $d(H_i, W_0) = d_i$ for every $i$.

Grzesik, Kráľ and Lovász (Theorem 18) construct such graphs and reals for which every graphon
$W$ with $d(H_i, W) = d_i$ for all $i$ is weakly isomorphic to a member of a family none of whose
graphons is finitely forcible.

Source: L. Lovász (joint work with B. Szegedy), Extremal graphs and
graph limits, in Graph Theory, Oberwolfach Reports 7 (2010), no. 11, pp. 554-555, question 1, DOI
10.4171/OWR/2010/11; resolution: A. Grzesik, D. Kráľ and L. M. Lovász, Elusive extremal graphs,
Proc. Lond. Math. Soc. (3) 121 (2020), 1685-1736, DOI 10.1112/plms.12382, arXiv:1807.01141,
Conjecture 1 (Lovász): if some convergent sequence of graphs has limit densities d(H_i) = d_i for i
= 1, ..., ℓ, then some finitely forcible such sequence does; Theorem 18: there are a family W of
graphons, graphs H_1, ..., H_ℓ and reals d_1, ..., d_ℓ such that a graphon is weakly isomorphic to a
member of W if and only if d(H_i, W) = d_i for all i, and no graphon in W is finitely forcible; 'Our
main result (Theorem 18) implies that the conjecture is false', https://arxiv.org/abs/1807.01141.
-/
public theorem_wanted finitelyForcibleOptimum_refuted : ¬ finitelyForcibleOptimum

end MathlibExt.Combinatorics.FinitelyForcibleOptimumOWR4212Problem011Wanted
