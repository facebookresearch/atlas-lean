# Neural codes, good covers and local obstructions

A neural code is a set of subsets of the neurons, read as the patterns of neurons active together; it is convex, or a good-cover code, when some convex, or contractible, open sets in Euclidean space realize exactly these patterns. Local obstructions are links in its simplicial complex that are not contractible.

Let $[n] = \{1, \dots, n\}$.

- A *neural code* $\mathcal{C}$ on $n$ neurons is a subset of $2^{[n]}$; its elements are *codewords*. A collection $\mathcal{U} = \{U_1, \dots, U_n\}$ of sets in a stimulus space $X \subseteq \mathbb{R}^d$ *realizes* $\mathcal{C}$ if for every $\sigma \subseteq [n]$,

$$
\sigma \in \mathcal{C} \iff \bigcap_{i \in \sigma} U_i \setminus \bigcup_{j \notin \sigma} U_j \neq \emptyset ,
$$

  with the empty intersection equal to $X$.
- $\mathcal{C}$ is *convex* if it is realized by [convex](../../../Geometry/convex-geometry/convex-set.md) open sets, and a *good-cover code* if it is realized by contractible open sets all of whose nonempty intersections are contractible (a *good cover*).
- The *simplicial complex of the code* $\Delta(\mathcal{C})$ is the smallest simplicial complex on $[n]$ containing $\mathcal{C}$. For a face $\sigma$ of a simplicial complex $\Delta$, the *link* is $\mathrm{Lk}_\sigma(\Delta) = \{\tau \in \Delta : \sigma \cap \tau = \emptyset,\ \sigma \cup \tau \in \Delta\}$.
- A face $\sigma$ of $\Delta$ is a *mandatory codeword* if $\mathrm{Lk}_\sigma(\Delta)$ is not contractible (its geometric realization is not a contractible space). $\mathcal{C}$ is *locally good* if it contains every mandatory codeword of $\Delta(\mathcal{C})$; this is equivalent to the absence of local obstructions in any realization by open sets.
- $\mathcal{C}$ is *$k$-sparse* if $|\sigma| \le k$ for all $\sigma \in \mathcal{C}$, that is, $\dim \Delta(\mathcal{C}) \le k - 1$.

Convex codes are good-cover codes, and good-cover codes are locally good; Chen, Frick and Shiu proved that a code is locally good exactly when it is a good-cover code. The converse of the first implication fails: a code on five neurons is a good-cover code but not convex (Lienkaemper, Shiu and Woodstock).

## Depends on

- [Finite abstract simplicial complex](../rational-homology-of-simplicial-complexes/is-simplicial-complex.md)
- [Contractible space](../../../Topology/algebraic-topology/contractibility-and-local-contractibility/contractible-space.md)
- [Convex set](../../../Geometry/convex-geometry/convex-set.md)

## Proof depends on

None.

## Expansion

A finite code is given by listing its codewords, so the questions whether it is convex, a good-cover code or locally good are decision problems about finite combinatorial data. Local goodness is a condition on finitely many links, the links of intersections of maximal codewords (Curto et al.), but checking it requires deciding contractibility of finite simplicial complexes, which is where undecidability enters.

## Sources

- Aaron Chen, Florian Frick and Anne Shiu, *Neural codes, decidability, and a new local obstruction to convexity*, SIAM Journal on Applied Algebra and Geometry 3 (2019), no. 1, 44–66, https://doi.org/10.1137/18M1186563; read as arXiv:1803.11516v2: Definitions 2.1, 2.3, 2.6, 2.7, 2.9, 2.14, 2.17 and 4.1, Propositions 2.15, 2.16 and 2.18, and Theorem 3.13 (locally good codes are good-cover codes).
