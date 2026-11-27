# Nullstellensatz size and degree equal reversible pebbling time and space

For a single-sink DAG $G$, a reversible pebbling of $G$ in time $t$ and space $s$ exists if and only if the pebbling contradiction of $G$ has a Nullstellensatz refutation of size at most $t+1$ and degree at most $s$, over any field; pebbling time-space trade-offs therefore become Nullstellensatz size-degree trade-offs.

Let $G = (V, E)$ be a DAG of constant fan-in with a unique sink $z$. A **reversible pebbling** of $G$ is a sequence of vertex sets $\mathbb{P}_0, \dots, \mathbb{P}_\tau$ with $\mathbb{P}_0 = \mathbb{P}_\tau = \emptyset$ and $z \in \bigcup_t \mathbb{P}_t$, where each step either places a pebble on a vertex $v \notin \mathbb{P}_{t-1}$ all of whose predecessors carry pebbles or removes a pebble from a vertex $v \in \mathbb{P}_{t-1}$ all of whose predecessors carry pebbles; its time is $\tau$ and its space $\max_t |\mathbb{P}_t|$. A **Nullstellensatz refutation** of polynomials $p_1, \dots, p_m$ is an identity $\sum_i r_i p_i + \sum_j s_j (x_j^2 - x_j) = 1$; its degree is the maximum degree of the products $r_i p_i$ and $s_j (x_j^2 - x_j)$, and its size is the total number of monomials when all products are expanded as linear combinations of monomials. A clause $\bigvee_{x \in P} x \vee \bigvee_{y \in N} \neg y$ is encoded as $\prod_{x \in P} (1 - x) \prod_{y \in N} y$.

**Theorem.** Let $G$ be a DAG with a single sink, $\phi$ its pebbling contradiction, and $\mathbb{F}$ a field. There is a reversible pebbling strategy for $G$ with time at most $t$ and space at most $s$ if and only if there is a Nullstellensatz refutation of $\phi$ over $\mathbb{F}$ of size at most $t + 1$ and degree at most $s$. The same holds for multilinear Nullstellensatz refutations.

**Example trade-off.** There is a family of 3-CNF formulas $F_n$ of size $\Theta(n)$ such that $F_n$ has a Nullstellensatz refutation of degree $O(\sqrt[6]{n} \log n)$, and a refutation of near-linear size and degree $O(\sqrt[3]{n} \log n)$, but every Nullstellensatz refutation of degree at most $\sqrt[3]{n}$ has exponential size.

## Expansion

Write $x_{\mathbb{P}} = \prod_{v \in \mathbb{P}} x_v$. For a pebbling that first reaches the sink at step $t'$ (one may assume $t = 2t'$), each step $i$ placing or removing $v_i$ gives $x_{\mathbb{P}_{i-1}} - x_{\mathbb{P}_i} = \pm\, x_{R_i} A_{v_i}$, where $A_{v_i}$ is the axiom of $v_i$ and $R_i$ the other pebbled vertices; summing telescopes to $1 - x_{\mathbb{P}_{t'}}$, and adding the sink axiom times $x_{\mathbb{P}_{t'} \setminus \{z\}}$ yields a refutation whose degree is the space and whose size is governed by the time. The converse extracts a reversible pebbling from the monomials of a refutation. The reductions are exact up to additive constants and go in both directions. Known reversible pebbling time-space trade-offs for Carlson-Savage graphs, stacks of superconcentrators and permutation graphs then give the trade-offs, the example coming from Carlson-Savage graphs.

## Depends on

- [Pebbling formulas of directed acyclic graphs](../../resolution-separations-and-supercritical-tradeoffs/pebbling-formula.md)

## Proof depends on

None.

## Sources

- Susanna F. de Rezende, Jakob Nordström, Or Meir, Robert Robere, "Nullstellensatz size-degree trade-offs from reversible pebbling", *34th Computational Complexity Conference (CCC 2019)*, LIPIcs 137, 2019, https://doi.org/10.4230/LIPIcs.CCC.2019.18; numbering of arXiv:2001.02481v1 (Theorems 1.1 and 3.1, Sections 2 and 4).
