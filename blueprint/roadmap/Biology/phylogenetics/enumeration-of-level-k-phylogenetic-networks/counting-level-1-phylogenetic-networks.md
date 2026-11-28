# Counting level-1 phylogenetic networks

A **binary rooted phylogenetic network** on a finite leaf set $X$ with $|X| \ge 2$ is a directed acyclic graph without multiple arcs, with one root (in-degree 0, out-degree 2), leaves (in-degree 1, out-degree 0) bijectively labelled by $X$, tree vertices (in-degree 1, out-degree 2) and reticulations (in-degree 2, out-degree 1), such that every *nontrivial* bridgeless component (one with at least two vertices) is the tail end of at least two cut arcs leaving it (no redundant blobs). On a singleton $X = \{x\}$ the only rooted network is the single vertex labelled $x$. It has **level $k$** if every bridgeless component contains at most $k$ reticulations. In a level-1 network (rooted galled tree) every nontrivial bridgeless component is a cycle formed by two directed paths from a source to a single reticulation. An **unrooted** binary network on $X$, $|X| \ge 2$, is a connected loopless graph whose vertices have degree 3 (internal vertices) or degree 1 (leaves, bijectively labelled by $X$), each nontrivial bridgeless component meeting at least 3 cut edges; it has level 1 when every such component is a cycle. Connectedness excludes, for example, two disjoint edges joining four labelled leaves. These definitions correct the source as printed in two places. Section 2.1 (5) reads "for each bridgeless component B of N, there exist at least two cut arcs of N whose tail belongs to B and whose head does not belong to B"; a leaf is a one-vertex bridgeless component (its incoming arc is a cut arc) with no outgoing arc, so read literally (5) fails at every leaf and admits no network with $|X| \ge 2$; the condition is meant for the nontrivial components. Section 2.2 defines an unrooted network as "a loopless (undirected) graph" with no connectedness requirement, so two disjoint edges joining four labelled leaves would qualify, as an "unrooted binary phylogenetic tree" and hence a level-1 network, and the three ways of pairing four leaves would raise $g_3 = 15$ below to $18$.

**Theorem (unrooted level-1).** For $n \ge 1$ let $g_n$ be the number of unrooted level-1 networks with $n + 1$ labelled leaves and $G(z) = \sum_{n \ge 1} g_n z^n / n!$. Then

$$G(z) = z + \tfrac12 G(z)^2 + \tfrac12 \frac{G(z)^2}{1 - G(z)}, \qquad\text{equivalently}\qquad G = z\,\varphi(G), \quad \varphi(u) = \frac{2 - 2u}{u^2 - 4u + 2},$$

so $g_n = (n-1)!\,[u^{n-1}]\,\varphi(u)^n$ by Lagrange inversion. The sequence $(g_n)_{n \ge 1}$ begins $1, 2, 15, 192, 3450$, and $g_n \sim c_1\, c_2^{\,n}\, n^{n-1}$ with $c_1 \approx 0.20748$, $c_2 \approx 1.89004$.

**Theorem (rooted level-1).** For $n \ge 1$ let $r_n$ be the number of rooted level-1 networks with $n$ labelled leaves, so that $r_1 = 1$ counts the one-vertex network, and $R(z) = \sum_{n \ge 1} r_n z^n / n!$. Then

$$R = z + \tfrac12 R^2 + \frac{R^2}{1 - R} + \tfrac12 \frac{R^3}{(1 - R)^2}, \qquad\text{equivalently}\qquad R = z\,\varphi(R), \quad \varphi(u) = \frac{1}{1 - \frac{u}{2} - \frac{u}{1 - u} - \frac12\big(\frac{u}{1-u}\big)^2}.$$

$R$ is algebraic with radius of convergence $1/8$ and has an explicit closed form in $\sqrt{1 - 8z}$. The sequence $(r_n)_{n \ge 1}$ begins $1, 3, 36, 723, 20280, 730755$, and

$$r_n \sim c_1\, (8/e)^n\, n^{n-1}, \qquad c_1 \approx 0.1339,$$

so $c_2 = 8/e \approx 2.943$.

**Parameters.** In both models, let $X_n$ be the number of cycles and $Y_n$ the number of edges (arcs) lying on cycles of a network drawn uniformly at random from the networks of fixed size $n$ (rooted level-1 networks with $n$ labelled leaves, or unrooted ones with $n + 1$). Then $X_n$ and $Y_n$ are asymptotically normal: $\mathbb{E} X_n = \mu_X n + O(1)$, $\operatorname{Var} X_n = \sigma_X^2 n + O(1)$ and $(X_n - \mathbb{E}X_n)/\sqrt{\operatorname{Var} X_n} \to \mathcal{N}(0,1)$ in distribution, and likewise for $Y_n$.

## Proof depends on

- [Lagrange–Bürmann formula from the fixed-point equation alone](../../../RingTheory/formal-power-series/lagrange-inversion-theorem/fps-lagrange-burmann-coeff.md)

## Expansion

Decompose at the root (rooted case) or at a distinguished leaf (unrooted case). In the rooted case the root is either a tree vertex with an unordered pair of independent subnetworks (the term $\tfrac12 R^2$) or the source of a cycle; a cycle is encoded by the possibly empty sequences of subnetworks hanging from its two sides, each contributing a factor $1/(1-R)$, and the subnetwork below its reticulation, with the no-multiple-arc and no-redundant-blob conditions removing degenerate cycles. The single leaf is the base case $z$. Because the specification has the form $R = z\varphi(R)$ with $\varphi$ analytic at $0$ and $\varphi(0) = 1$, the Lagrange–Bürmann formula with $g = X$, $n\,[z^n]R = [u^{n-1}]\varphi(u)^n$, gives exact formulas, and the singular inversion theorem (square-root singularity at $\rho = \tau/\varphi(\tau)$, where $\varphi(\tau) = \tau \varphi'(\tau)$) gives $[z^n] R \sim \gamma \rho^{-n} n^{-3/2}$; multiplying by $n!$ via Stirling yields the $c_1 c_2^n n^{n-1}$ shape with $c_2 = 1/(e\rho)$. Marking cycles and cycle edges by extra variables and applying a Drmota–Lalley–Woods type central limit theorem gives the normal limits. The unrooted level-1 equation recovers the Semple–Steel enumeration of galled trees.

## Sources

- M. Bouvel, P. Gambette and M. Mansouri, "Counting phylogenetic networks of level 1 and 2", Journal of Mathematical Biology (2020), Sections 2, 4 and 5 (Theorem 4.1, Propositions 4.2, 4.3, Theorem 5.1, Propositions 5.2, 5.3, 5.5, Table 2), <https://doi.org/10.1007/s00285-020-01543-5>.
- C. Semple and M. Steel, "Unicyclic networks: compatibility and enumeration", IEEE/ACM Transactions on Computational Biology and Bioinformatics 3 (2006).
