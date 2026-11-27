# Kirchhoff's effective resistance formula, weighted

Let $G$ be a finite connected simple graph with vertex set $V$ and $c$ a real function on unordered pairs of vertices with $c(e) > 0$ for every edge $e$ of $G$. Draw a spanning tree $T$ of $G$ with probability proportional to $\Xi(T) = \prod_{e \in T} c(e)$. Then for every edge $uv$ of $G$,

$$\mathbb{P}[uv \in T] = \frac{\sum_{T \ni uv} \prod_{e \in T} c(e)}{\sum_{T} \prod_{e \in T} c(e)} = c(uv)\, R(u \leftrightarrow v),$$

the sums running over the spanning trees of $G$ (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Section 4.2, Kirchhoff's Effective Resistance Formula). Here $R(u \leftrightarrow v)$ is the [effective resistance](effective-resistance.md) of the multigraph of darts of $G$, each dart $d$ carrying conductance $c(d)/2$ for its underlying edge, which is the network $G$ with conductances $c$.

This is the source's statement for finite networks, with $G$ simple and the conductances given on its edges; values of $c$ off the edges of $G$ play no role. With $c \equiv 1$ it reduces to the [unit-conductance formula](kirchhoff-effective-resistance-formula.md). Connectivity makes the denominator positive.

## Background

- [Weighted matrix-tree theorem](weighted-matrix-tree.md): the denominator $\Xi(G)$ as a determinant.
- [Foster's identity](sum-mul-effective-resistance.md): summing $c(e)\, R(e^- \leftrightarrow e^+)$ over the edges gives $n - 1$, the number of edges of every spanning tree.
