# Conductance and Cheeger's inequality

The conductance $\varphi(S) = w(\partial S) / \min(d(S), d(V \setminus S))$ of a vertex set in a weighted graph and the hard direction of Cheeger's inequality: from any vector $z$ that is centred with respect to the weighted degrees and has $z^{\mathsf T} D z > 0$ and small Rayleigh quotient $z^{\mathsf T} L z / z^{\mathsf T} D z$, a threshold cut $\{a : z(a) < \tau\}$ has conductance at most $\sqrt{2 z^{\mathsf T} L z / z^{\mathsf T} D z}$ (D. A. Spielman, *Spectral and Algebraic Graph Theory*, Chapter 21, following Trevisan). The topic has both directions: the easy direction $\nu_2/2 \le \varphi(S)$ in variational form (Lemma 20.3.1 and inequality (20.2)) and the hard direction for any degree-centred vector (Theorem 21.1.3).

- [Weighted degree](weighted-degree.md)
- [Weighted degrees are nonnegative](weighted-degree-nonneg.md)
- [Volume of a vertex set](volume.md)
- [Easy direction of Cheeger's inequality for conductance](mul-volume-mul-volume-compl-le-of-forall.md)
- [Cheeger's inequality, hard direction](exists-threshold-cut-le-sqrt.md)

## Related topics

- [Graph Laplacians and Cheeger's inequality](../../part-01/graph-laplacians-and-cheeger-s-inequality/README.md): the Laplacian, its quadratic form and the easy direction $\lambda_2/2 \le \theta_G$.
- [Expander graphs](../../../graph-families-and-operations/expander-graphs/README.md): Cheeger's inequality turns a spectral gap into edge expansion.
- [Canonical paths and multicommodity flow](../../../../Probability/markov-chains/canonical-paths-and-multicommodity-flow/README.md): the Markov-chain counterpart: conductance and congestion of path systems in a reversible chain, viewed as a graph with edge weights $\pi(u) P(u, v)$.
