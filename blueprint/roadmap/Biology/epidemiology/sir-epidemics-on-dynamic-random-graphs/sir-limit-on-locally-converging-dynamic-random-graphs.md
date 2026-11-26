# SIR limit on locally converging dynamic random graphs

**Setting.** Let $(G_n^s)_{s\in[0,T]}$ be a *dynamic graph* on the fixed vertex set $[n]$ whose edge set changes over time. Its *time-marked union graph* $G_n^{[0,T]}$ is the union of all edges ever present, each edge marked by the set of times at which it is present. Suppose the uniformly rooted time-marked union graphs converge *locally in probability* to a random rooted time-marked graph with law $\mu$ on $\mathcal G_\star$. Run an SIR epidemic on $(G_n^s)$ with general (not necessarily exponential) infection and recovery times. Infection can pass along an edge only while the edge is present. Initially every vertex is infected independently with probability $\rho>0$. Let $\big(S_n(t),I_n(t),R_n(t)\big)$ be the fractions of susceptible, infected and recovered vertices.

**Theorem.** For every $t\in[0,T]$,

$$\big(S_n(t),I_n(t),R_n(t)\big)\xrightarrow{\ \mathbf P\ }\big(s(t),i(t),r(t)\big),$$

where $s(t)=\mu(o\in\mathcal S(t))$, $i(t)=\mu(o\in\mathcal I(t))$ and $r(t)=\mu(o\in\mathcal R(t))$ are the probabilities that the root $o$ is susceptible, infected or recovered at time $t$ in the same SIR epidemic run on the limiting dynamic graph, again with independent initial infections of density $\rho$.

The key quantitative inputs are the following.

- *Locality.* Let $(S_{n,r},I_{n,r},R_{n,r})$ be the epidemic in which each vertex sees only infections started within graph distance $r$. Then $\mathbf E\big[\sup_{t\le T}\|(S_n,I_n,R_n)(t)-(S_{n,r},I_{n,r},R_{n,r})(t)\|_\infty\big]\le(1-\rho)^r$, uniformly in the graph.
- *Concentration.* Conditionally on the graph, $\sup_{t\le T}\mathrm{Var}(S_{n,r}(t))\le \frac1n+\varepsilon_{2r}(G_n^{[0,T]})$, where $\varepsilon_{2r}$ is the fraction of vertex pairs within distance $2r$ in the union graph. This tends to $0$ under local convergence.

## Expansion

The positive initial density $\rho$ makes the epidemic local. Along any infection path of length $r$ into a vertex, the probability that none of the $r$ intermediate vertices was itself infected at time $0$ is at most $(1-\rho)^r$. A shortcut through an initially infected vertex then makes longer paths irrelevant. So the state of a typical vertex is, up to an error of $(1-\rho)^r$, a bounded continuous functional of its $r$-neighborhood in the time-marked union graph, and local convergence transfers its expectation to the limit. The variance bound gives concentration of the empirical fractions. The hypothesis is verified for the dynamic Erdős–Rényi graph, whose edges switch on and off independently, and for dynamic bipartite generalized random graphs and random intersection graphs, whose groups switch on and off and create overlapping cliques.

## Sources

- M. Milewska, R. van der Hofstad, B. Zwart, "SIR on locally converging dynamic random graphs", arXiv:2501.09623 (2025): Theorem 1.1 (dynamic convergence of the epidemic processes), Proposition 3.1 (first-moment local approximation), Proposition 3.2 and Lemma 4.1 (second-moment bounds), Section 6 (examples of converging dynamic random graphs). <https://doi.org/10.48550/arXiv.2501.09623>
