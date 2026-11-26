# Edge importance dichotomy on random graphs

Consider the edge importances $R_k$ of the stochastic shielding approximation for an Ornstein–Uhlenbeck process $dX = LX\,dt + \sum_k \sigma_k\zeta_k\,dW_k$ on a random graph with $n$ nodes and symmetric Laplacian $L$, and a binary measurement vector $M \in \{0,1\}^n$ with $0 < \sum_i M_i = O(1)$ observable nodes. For a binary $M$ and $\zeta_k = e_{j(k)} - e_{i(k)}$, $|M^{\top}\zeta_k| = 1$ when edge $k$ joins an observable and an unobservable node and $|M^{\top}\zeta_k| = 0$ when it joins two nodes with the same label.

**Theorem.** Assume the random graph ensemble satisfies the spectral hypotheses A0–A5 of the source (A0: independent symmetric edge weights $a_{ij} = a_{ji} \geq 0$ with common mean $\mu_A$, variance $\sigma_A^2 > 0$ and a bounded higher moment; A1: Laplacian eigenvalues and eigenvectors nearly independent, and their joint law nearly invariant under permuting eigenvectors; A2: eigenvector components have mean zero; A3: conditions on second-order moments of eigenvector components; A4: fourth moments of eigenvector components of order $n^{-q}$ for some $q > 1$; A5: mixed fourth-order products of distinct components are of smaller order). Then, as $n \to \infty$,

$$\mathbb{E}[R_k \mid M] = \frac{\sigma_k^2\,|M^{\top}\zeta_k|}{nC} + O(n^{-q}), \qquad q > 1,$$

where the constant $C$ depends on the mean edge weight (for the Erdős–Rényi ensemble with edge probability $p$, $C = 2p$).

Thus the edges split into two classes: edges between differently labeled nodes have mean importance of order $1/n$, while edges between identically labeled nodes have mean importance $O(n^{-q})$, asymptotically negligible. Suppressing the noise on all edges between indistinguishable states (the stochastic shielding rule) therefore loses only a vanishing fraction of the observed variance. For the symmetric Gaussian ensemble $q = 2$; for Erdős–Rényi graphs the hypotheses hold empirically with $q \approx 5/3$.

## Depends on

- [Stochastic shielding error as a sum of edge importances](stochastic-shielding-error-as-a-sum-of-edge-importances.md)

## Expansion

Start from the exact spectral formula $R_k = \sigma_k^2 \sum_{i,j \geq 2} \frac{-1}{\lambda_i + \lambda_j}(M^{\top}v_i)(v_i^{\top}\zeta_k)(\zeta_k^{\top}v_j)(v_j^{\top}M)$. If the nonzero eigenvalues cluster near $-nC$, the factor $-1/(\lambda_i + \lambda_j)$ is approximately $1/(2nC)$ and the double sum nearly factors into $\bigl(\sum_{i \geq 2}(M^{\top}v_i)(v_i^{\top}\zeta_k)\bigr)^2$ plus fluctuation terms. By completeness, $\sum_{i \geq 1} v_iv_i^{\top} = I$ and $v_1 \propto \mathbf{1}$ is orthogonal to $\zeta_k$, so the leading sum equals $M^{\top}\zeta_k$, which vanishes on edges between equally labeled nodes. What remains for those edges is controlled by eigenvalue spread and by fourth moments of the eigenvector components, giving the $O(n^{-q})$ term. Parts of the argument combine rigorous probabilistic estimates with numerically checked assumptions about the eigenvector statistics of the ensemble, so the result is conditional on A0–A5.

## Sources

- D. R. Schmidt, P. J. Thomas, "Measuring edge importance: a quantitative analysis of the stochastic shielding approximation for random processes on graphs", *Journal of Mathematical Neuroscience* 4 (2014) 6. Theorem 2 (Eq. 11), Section 3.1 (assumptions A0–A5, Remarks), Section 3.2 (proof, Lemma 3) and Section 3.3 (Erdős–Rényi ensemble, $C = 2p$). <https://doi.org/10.1186/2190-8567-4-6>. PMCID: PMC4234999.
