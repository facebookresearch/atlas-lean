---
article_id: af_5d6fa561562ab06aa6b910cf
declaration: theorem
origin: cited
lean: SimpleGraph.rw_convergence_conductance_bound
---

# Corollary 1

Let $G = (V, E)$ be a connected, undirected graph with $m$ edges and let $\pi(x)$ be its stationary distribution $\frac{d_x}{\sum_{v \in V} d_v}$. For every subset of vertices $W \subset V$ and every time $t$, if $x \equiv \sum_{w \in W} d_w$ and $\varphi(W)$ is the conductance of the cut $(W, \overline{W})$, then the following inequality holds: $$\left| \sum_{w \in W} p^t(w) - \pi(w) \right| \leq \min\!\left(\sqrt{x},\, \sqrt{2m - x}\right) \left(1 - \frac{1}{2}\varphi(W)^2\right)^t.$$

## Depends on

- [Definition 7 (Conductance)](../section-6/043-conductance.md)

## Proof depends on

- [Theorem 11 (Lovasz-Simonovits)](../lecture-7/075-lovasz-simonovits.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Lecture 8, Section 2.4](../../../../../sources/v1/AnAlgorithmistsToolkit.md)
