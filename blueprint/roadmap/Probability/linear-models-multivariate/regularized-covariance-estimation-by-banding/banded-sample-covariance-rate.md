# Bickel–Levina rate for the banded sample covariance

Let $X_1, \dots, X_n$ be i.i.d. $N_p(0, \Sigma)$ with $p = p_n \ge 2$, and let

$$\hat\Sigma = \frac1n \sum_{i=1}^n (X_i - \bar X)(X_i - \bar X)^{\mathsf T}$$

be the sample covariance (Bickel and Levina's equation (1)). Fix $\varepsilon_0, \alpha, C > 0$ and assume $\log p_n / n \to 0$. With the band width and rate

$$k_n = \Bigl\lceil \Bigl(\frac{\log p_n}{n}\Bigr)^{-1/(2(\alpha+1))} \Bigr\rceil, \qquad r_n = \Bigl(\frac{\log p_n}{n}\Bigr)^{\alpha/(2(\alpha+1))},$$

the banded estimator $B_{k_n}(\hat\Sigma)$ ([banding operator](band.md)) satisfies

$$\|B_{k_n}(\hat\Sigma) - \Sigma\| = O_P(r_n) \quad\text{and}\quad \|B_{k_n}(\hat\Sigma)^{-1} - \Sigma^{-1}\| = O_P(r_n)$$

in operator norm, uniformly over $\Sigma$ in the [bandable class](bandable-class.md) $\mathcal U(\varepsilon_0, \alpha, C)$: for every $\eta > 0$ there are $K$ and $N$ such that for all $n \ge N$ and all $\Sigma \in \mathcal U(\varepsilon_0, \alpha, C)$, each of the events $\{\|\cdot\| > K r_n\}$ has probability at most $\eta$.

The paper takes any $k_n \asymp (n^{-1} \log p)^{-1/(2(\alpha+1))}$; the statement above fixes the ceiling. The hypothesis $\log p_n / n \to 0$ is the regime of the paper's abstract and of its proof, whose tail bounds are applied at $t \asymp (n^{-1} \log p)^{1/2}$ in a bounded range; $p_n \ge 2$ keeps $\log p_n > 0$. The inverse of a singular matrix is taken to be $0$; with probability tending to one uniformly over the class $B_{k_n}(\hat\Sigma)$ is invertible, so this convention does not affect the statement.

The proof splits $\|B_k(\hat\Sigma) - \Sigma\| \le \|B_k(\hat\Sigma) - B_k(\Sigma)\| + \|B_k(\Sigma) - \Sigma\|$. The bias is at most $C k^{-\alpha}$ on the class, and the variance term is at most $(2k + 1) \max_{ij} |\hat\sigma_{ij} - \sigma_{ij}|$, both by the Schur-test inequality (A2); the entrywise maximum is $O_P((n^{-1} \log p)^{1/2})$ by a union bound over the entries with exponential tail bounds. Balancing $k^{-\alpha}$ against $k (n^{-1} \log p)^{1/2}$ gives $k_n$ and $r_n$.

## Informally uses

- [Uniform bias bound on the bandable class](norm-band-sub-le-of-mem-bandable-class.md): the bias term (A6).
- [Operator norm of a banded matrix](norm-band-le.md): the variance term, from the entrywise error.
- [Bernstein-type tail bounds](../../concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/README.md): exponential tail bounds for the entries $\hat\sigma_{ij} - \sigma_{ij}$, products of Gaussians, which the paper takes from Saulis and Statulevičius (its Lemma A.3).

## Background

- [Matrix Bernstein inequality](../../concentration-inequalities/matrix-concentration-inequalities/matrix-bernstein.md): the operator-norm concentration of sums of random matrices, a route to sample-covariance bounds without banding.
- [Principal component analysis](../principal-component-analysis/README.md): Bickel and Levina's Section 4 deduces consistency of eigenvalues and eigenvectors from operator-norm consistency.

## Sources

- P. J. Bickel and E. Levina, "Regularized estimation of large covariance matrices", *Ann. Statist.* 36 (2008) 199–227, Theorem 1 and its proof in the Appendix.
