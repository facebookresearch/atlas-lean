# Splitting probabilities as spanning-forest ratios

**Setting.** A linear-framework graph $G$ is a finite, simple, directed graph on vertices
$\{1,\dots,N\}$ with positive edge labels $\ell(i \to j)$ (transition rates), connected when edge
directions are ignored. Its Laplacian has entries $L(G)_{ij} = \ell(j \to i)$ for $i \ne j$ with
$j \to i$, $0$ for other $i \ne j$, and $L(G)_{jj} = -\sum_k \ell(j \to k)$, so the master equation is
$\dot x = L(G) x$. The weight $w(H)$ of a subgraph is the product of its edge labels, and the weight of a
set of subgraphs is the sum of their weights. A **spanning forest** contains every vertex, no cycle
(ignoring directions), and at most one outgoing edge per vertex; its roots are the vertices without
outgoing edge. $\Phi_A(G)$ is the set of spanning forests rooted exactly at $A$, and for $\#A = \#B$,
$\Phi_{B \to A}(G) \subseteq \Phi_A(G)$ consists of those in which each vertex of $B$ has a path to a
distinct root in $A$.
Let $X(t)$ be the continuous-time Markov process with jump rates $\ell(i\to j)$. Suppose every terminal
strongly connected component of $G$ is a single vertex, and let $Z$ be the set of these terminal
vertices. For $z \in Z$ let $V^-_{\mathrm{in}}(z)$ be the non-terminal vertices with a directed path to
$z$. The **splitting probability** $\pi_{i,z}$ is the probability that $X$ started at $i$ is ever
absorbed at $z$.

**Theorem 4.** For every $U \subseteq V(G)$ with $Z \subseteq U \subseteq \overline{V^-_{\mathrm{in}}(z)}$
and every $i \in V^-_{\mathrm{in}}(z)$,

$$\pi_{i,z} = \frac{w\big(\Phi_{(U\setminus\{z\})\cup\{i\} \to U}(G)\big)}{w\big(\Phi_U(G)\big)}.$$

The denominator weighs all spanning forests rooted at $U$, the numerator those in which $i$ has a path
to $z$, so $0 < \pi_{i,z} \le 1$. For a graph with a single terminal vertex, $\pi_{i,z} = 1$ for every $i$.
A general graph reduces to this case: to study first passage from $i$ to any vertex $v$, delete the
outgoing edges of $v$ and of every vertex in a terminal component not containing $v$, and keep the
connected component of $v$; its terminal components are singletons and the probabilities of reaching
$v$ by time $t$ are unchanged (Lemma 8).

## Proof depends on

- [Spanning-forest formula for inverses of Laplacian submatrices](spanning-forest-formula-for-inverses-of-laplacian-submatrices.md)

## Expansion

The probability $p_{i,z}(t)$ of having reached $z$ by time $t$ obeys the adjoint (backward) master
equation $\frac{d}{dt}p_{i,z} = \sum_{j} \ell(i\to j)p_{j,z} - \lambda_i p_{i,z}$, with $\lambda_i$ the
total exit rate. Its derivative $u_{i,z}$ has Laplace transform
$\tilde u_z(s) = (sI + \mathcal L[V^-_{\mathrm{in}}(z), V^-_{\mathrm{in}}(z)])^{-1} v$ with
$\mathcal L = -L(G)^{\mathsf T}$ and $v_j = \ell(j\to z)$, and $\pi_{i,z} = \tilde u_{i,z}(0)$. The block
upper-triangular structure of $\mathcal L[\bar U,\bar U]$ lets one replace the index set by any admissible
$\bar U$, the inverse is given by spanning forests, and the edge-adjoining bijection collapses the
resulting sum over $j$ into the single forest weight in the numerator.

## Sources

- K.-M. Nam, J. Gunawardena, "Algebraic formulas for first-passage times of Markov processes in the linear framework", Bulletin of Mathematical Biology 87(11) (2025) 161, <https://doi.org/10.1007/s11538-025-01524-z> (PMC12521310). Section 3.1 (definitions, Eqs. 25–32), Eqs. (33)–(48), Theorem 4 (Eq. 49), Eq. (56), Lemma 8.
