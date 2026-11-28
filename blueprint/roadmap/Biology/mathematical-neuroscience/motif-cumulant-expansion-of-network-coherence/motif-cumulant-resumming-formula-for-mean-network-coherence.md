# Motif-cumulant resumming formula for mean network coherence

**Model.** $N$ linearly interacting stochastic units (for example, linearized neurons or a multivariate Ornstein–Uhlenbeck network) with activity

$$y_i(t)=x_i(t)+A(t)*\sum_j W_{ij}\,y_j(t),\qquad W=w\,W^0,$$

where $W^0$ is a $0/1$ adjacency matrix, $w$ a uniform coupling weight, $A$ a common linear response kernel ($*$ is convolution) and the baselines $x_i$ are i.i.d. with power spectrum $S_x$. In the frequency domain (at $\omega=0$, total covariance), if the spectral radius of $\tilde A W$ is below $1$ then $S_y=(I-\bar{\tilde A}W)^{-1}S_x(I-\tilde AW^T)^{-1}$. Write $\langle X\rangle$ for the mean of the entries of a matrix and $g=N\tilde A w$.

**Motif moments and cumulants.** The motif moment $\mu_{n,m}=\langle (W^0)^n(W^{0T})^m\rangle/N^{n+m-1}$ is the empirical frequency of $(n,m)$ motifs (two directed paths of lengths $n$ and $m$ from a common source), with $\mu_n=\mu_{n,0}$ and $\mu_{0,0}=1$. Motif cumulants $\kappa_n,\kappa_{n,m}$ are defined recursively over compositions $\mathcal C(n)$ (ordered partitions) of $n$:

$$\mu_n=\sum_{(n_1,\dots,n_t)\in\mathcal C(n)}\prod_{i=1}^t\kappa_{n_i},$$

$$\mu_{n,m}=\sum_{\substack{(n_1,\dots,n_t)\in\mathcal C(n)\\(m_1,\dots,m_s)\in\mathcal C(m)}}\Big(\prod_{i=2}^t\kappa_{n_i}\Big)\big(\kappa_{n_1,m_1}+\kappa_{n_1}\kappa_{m_1}\big)\Big(\prod_{j=2}^s\kappa_{m_j}\Big).$$

So $\kappa_1=\mu_1$ is the connection probability, and higher cumulants measure the excess of a motif over what its sub-motifs predict (they vanish in expectation for an Erdős–Rényi graph).

**Theorem.** For this network the mean coherence (covariance averaged over all pairs) is

$$\frac{\langle S_y\rangle}{S_x}=\frac1N\Big(1-\sum_{n\ge1}g^n\kappa_n\Big)^{-2}\Big(1+\sum_{n,m\ge1}g^{n+m}\kappa_{n,m}\Big),$$

whereas the motif-moment expansion reads $\langle S_y\rangle/S_x=\frac1N\sum_{n,m\ge0}g^{n+m}\mu_{n,m}$.

## Expansion

Expanding the resolvents gives $S_y/S_x=\sum_{n,m}\bar{\tilde A}^n\tilde A^m W^n(W^T)^m$: covariance is a sum over pairs of paths with a common source. Averaging gives the moment series, whose truncation at order $k_{\max}$ drops all longer paths. The cumulant recursion is the combinatorial analogue of the moment–cumulant relation: summing the composition formulas over all lengths factorizes the chain motifs into the geometric factor $(1-\sum g^n\kappa_n)^{-1}$ for each branch, leaving only the irreducible two-branch cumulants. Truncating the cumulant series therefore keeps contributions of paths of every length, predicting high-order motif frequencies from low-order ones, and approximates coherence far better than truncated moments when the network is homogeneous. For heterogeneous networks the same formula holds blockwise with subpopulation cumulants, and an analogous resummation over set partitions with Faà di Bruno coefficients extends it to $k$-th order correlations, where only a restricted family of $k$-branch motifs contributes.

## Sources

- Y. Hu, J. Trousdale, K. Josić and E. Shea-Brown, *Local paths to global coherence: cutting networks down to size*, arXiv:1212.4239 (2012); Section III (Moments, cumulants, and network-wide coherence), main theorem and motif-cumulant recursion; Sections IV–V for the subpopulation and higher-order extensions. <https://doi.org/10.48550/arXiv.1212.4239>
