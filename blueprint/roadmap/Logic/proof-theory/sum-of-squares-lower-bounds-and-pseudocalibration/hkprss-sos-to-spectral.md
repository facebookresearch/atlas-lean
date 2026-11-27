# Hopkins et al.: SoS distinguishers for noise-robust problems yield spectral distinguishers

Let $\nu$ (null) and $\mu$ (planted) be distributions on instances $I \in A^N$, and let $\mathcal{S}$ be a system of $n^{O(d)}$ polynomial constraints of degree at most $2d$ in program variables $x \in \mathbb{R}^n$ and constant degree $k$ in the instance variables. Suppose that

1. for $I \sim \nu$, with high probability $\mathcal{S}$ has a degree-$d$ sum-of-squares refutation with polynomially bounded coefficients;
2. $\mathcal{S}$ is *robustly inferable* for $\mu$: from a random sub-instance $I_S$ of $I \sim \mu$ (coordinates in a random set $S$ drawn from a subsampling distribution $\Theta$) one can infer a solution that stays feasible, with overwhelming probability, when the coordinates outside $S$ are re-randomized according to $\nu$;
3. $\Theta$ rarely contains large sets of coordinates, at a rate tied to a degree parameter $D$.

Then there is a square matrix $Q(I)$, indexed by tuples in $[n]^{\le d}$, whose entries are polynomials of degree $O(D)$ in the instance such that the expected largest non-negative eigenvalue $\lambda^+_{\max}(Q(I))$ under $\mu$ exceeds that under $\nu$ by a factor $n^{\Omega(B)}$, where $n^{B}$ bounds the refutation coefficients. In words: for noise-robust planted problems, degree-$d$ SoS is no stronger than spectral tests on $n^{O(d)}$-dimensional matrices with low-degree polynomial entries, which covers random CSP refutation, tensor and sparse PCA, densest-$k$-subgraph, community detection and planted clique. This does not say that SoS is no stronger than scalar low-degree polynomial tests, since $\lambda^+_{\max}$ is not itself a low-degree polynomial; that stronger statement is the authors' Conjecture 1.2.

## Proof sketch

Argue by contradiction: assume no degree-$2D$ matrix polynomial distinguishes $\mu$ from $\nu$; then scalar degree-$D$ polynomials have comparable norms under $\mu$ and $\nu$. For each subsampled set $S$, weight the moment matrix of the solution inferred from $I_S$ by the relative density $\mu/\nu$ averaged over completions of $I_S$, and average over $S \sim \Theta$. Robust inference makes the result nearly feasible for the SoS relaxation, and since each term depends only on $I_S$, the average involves only low-degree functions of the instance; the no-distinguisher assumption then transfers its near-feasibility and positivity to null instances. This yields an approximate degree-$d$ pseudo-distribution for $I \sim \nu$, contradicting the SoS refutation.

## Depends on

- [The Lasserre / sum-of-squares hierarchy for Boolean polynomial optimization](lasserre-hierarchy.md)
- [Low-degree likelihood ratio and low-degree advantage](../../../Probability/high-dimensional-probability/low-degree-likelihood-ratio-method/low-degree-likelihood-ratio.md)

## Sources

- S. B. Hopkins, P. K. Kothari, A. Potechin, P. Raghavendra, T. Schramm, D. Steurer, "The power of sum-of-squares for detecting hidden structures", FOCS (2017), arXiv:1710.05017.
