# Canonical paths and multicommodity flow

Sinclair's geometric bounds on the spectral gap of a reversible Markov chain (A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*, Combinatorics, Probability and Computing 1 (1992), 351–370). View the chain as a network in which the oriented edge $(u, v)$ has capacity $Q(u, v) = \pi(u) P(u, v)$, and route $\pi(x) \pi(y)$ units from every state $x$ to every other state $y$, along one canonical path or split over several paths (a multicommodity flow). If no edge is overloaded, the chain has no bottleneck: the congestion bounds the conductance from below (Theorem 3), and the length-weighted congestion bounds the spectral gap directly (Theorem 5 for paths, Theorem 5′ for flows; a modification of the Diaconis–Stroock bound). Both go through a Poincaré inequality, which also bounds the mixing time of the lazy chain (see the mixing-times topic). Conversely a chain that mixes in $\tau$ steps supports a flow with congestion at most $16 \tau$ (Theorem 8, through its key Lemma 7), and the upper half of Cheeger's inequality for chains reads $\lambda_1 \le 1 - \Phi^2/2$. Sinclair concludes that rapid mixing, flows of polynomially bounded congestion and inverse-polynomial conductance are equivalent, with two caveats. The gap controls mixing only once the smallest eigenvalue is dealt with (for instance by making the chain lazy), and the mixing time from $x$ is bounded by $\bigl(\log(1/\pi(x)) + \log(1/\varepsilon)\bigr)$ divided by the absolute spectral gap (Proposition 1(i)), so a polynomial bound needs $\log(1/\pi(x))$, as well as the inverse gap, to be polynomially bounded.

- [Oriented edges of a path](path-edges.md)
- [Endpoint of a path](path-end.md)
- [Number of edges of a path](length-path-edges.md)
- [Telescoping along a path](sum-path-edges-sub.md)
- [A path leaving a set crosses its boundary](exists-mem-path-edges-of-mem-of-not-mem.md)
- [Flow of a path system through an oriented edge](path-load.md)
- [Length-weighted flow of a path system through an oriented edge](elongated-path-load.md)
- [Length-weighted load versus load](elongated-path-load-le-mul-path-load.md)
- [Regrouping a sum over a list of edges](sum-map-eq-sum-count.md)
- [Cauchy–Schwarz for a list](sq-sum-map-le.md)
- [Reindexing a fourfold sum](sum-sum-sum-sum-comm.md)
- [The canonical-path Poincaré inequality](sum-sq-sub-mul-le-of-elongated-path-load.md)
- [Eigenvectors for eigenvalues other than $1$ have mean zero](sum-mul-eq-zero-of-eigenvector.md)
- [A Poincaré inequality bounds the spectral gap, for an eigenvector orthogonal to constants](one-le-mul-one-sub-of-poincare-of-mean-z.md)
- [A Poincaré inequality bounds the spectral gap](one-le-mul-one-sub-of-poincare.md)
- [Sinclair's canonical-path bound on the spectral gap](one-le-mul-one-sub-of-eigenvector.md)
- [Canonical paths bound the spectral gap, for an eigenvector orthogonal to constants](one-le-mul-one-sub-of-eigenvector-of-mea.md)
- [Theorem 5 in the form $\mu \le 1 - 1/\bar\rho$](le-one-sub-inv-of-eigenvector.md)
- [Sinclair's Corollary 6: $\lambda_1 \le 1 - 1/(\rho \ell)$](le-one-sub-inv-mul-of-eigenvector.md)
- [Paths crossing a cut](mul-sum-compl-le-sum-path-load.md)
- [The cut bound $\pi(A)\pi(A^c) \le \rho\, Q(A, A^c)$](mul-sum-compl-le-of-path-load-le.md)
- [Sinclair's Theorem 3: $\Phi \ge 1/(2\rho)$](sum-le-two-mul-of-path-load-le.md)
- [Cheeger's inequality for reversible Markov chains, upper bound](le-one-sub-sq-div-two-of-eigenvector.md)
- [Multicommodity flow in a Markov chain](multicommodity-flow.md)
- [Flow through an oriented edge](load.md)
- [Length-weighted flow through an oriented edge](elongated-load.md)
- [The flow Poincaré inequality](sum-sq-sub-mul-le-of-elongated-load-le.md)
- [Sinclair's Theorem 5′: flows bound the spectral gap](one-le-mul-one-sub-of-eigenvector-2.md)
- [Inequality (13) for flows (hence Theorem 3′)](mul-sum-compl-le.md)
- [Sinclair's Theorem 3′: $\Phi \ge 1/(2\rho(f))$](sum-le-two-mul.md)
- [Detailed balance for powers](pow-detailed-balance.md)
- [Excess mass on a set is at most the total variation distance](sum-sub-le-tv-dist.md)
- [Sinclair's Lemma 7](div-eight-le-pow-apply.md)
- [Sinclair's Lemma 7 from a single mixing time](div-eight-le-pow-apply-of-is-mixed-at.md)
- [Rapid mixing implies a low-congestion flow](exists-multicommodity-flow-load-le-sixte.md)

## Related topics

- [Mixing times of Markov chains](../mixing-times-of-markov-chains/README.md): the total variation distance and the $1/4$-mixing time that Lemma 7 and Theorem 8 start from.
- [Kolmogorov's criterion for reversibility](../kolmogorov-s-criterion-for-reversibility/README.md): detailed balance, the standing hypothesis of every bound here.
- [Conductance and Cheeger's inequality](../../../GraphTheory/algebraic-graph-theory/part-02/conductance-and-cheeger-s-inequality/README.md): Cheeger's inequality for weighted graphs, the graph counterpart of the conductance bound for chains.
- [Graph Laplacians and Cheeger's inequality](../../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/README.md): the Laplacian quadratic form, which for edge weights $\pi(u) P(u, v)$ is the Dirichlet form compared with the variance here.
- [Complexity of the permanent](../../../TheoryOfComputation/counting-complexity/complexity-of-the-permanent/README.md): Sinclair's 1992 paper uses these path bounds to improve the running time of randomised approximation algorithms for the permanent of a 0-1 matrix, which work by sampling from a Markov chain on matchings.
- [Markov chain Monte Carlo](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/markov-chain-monte-carlo/README.md): the sampling algorithms whose running time these bounds control.
- [Dirichlet forms](../dirichlet-forms/README.md): the Poincaré inequalities of this topic are lower bounds on the spectral gap of the Dirichlet form.
- [Effective resistance and electrical networks](../../../GraphTheory/algebraic-graph-theory/part-01/effective-resistance-and-electrical-networks/README.md): single-commodity unit flows in the same network, whose least energy is an effective resistance (Thomson's principle).
