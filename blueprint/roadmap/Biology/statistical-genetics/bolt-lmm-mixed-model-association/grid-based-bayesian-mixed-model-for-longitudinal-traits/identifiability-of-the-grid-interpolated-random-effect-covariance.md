# Identifiability of the grid-interpolated random-effect covariance

For individuals $i = 1,\dots,n$ with $n_i$ phenotype measurements at arbitrary times, consider the mixed model

$$y_i = \mu\mathbf 1_{n_i} + x_i\Gamma\beta + p_i\nu_i + e_i, \qquad \nu_i \sim \mathcal N(0, D), \qquad e_i \sim \mathcal N(0, \sigma^2 I_{n_i}),$$

where $\beta$ collects genetic main effects, time/environment effects, epistatic and gene–time interactions with selection indicators in $\Gamma$, and $\nu_i \in \mathbb{R}^k$ are random effects at $k$ fixed grid times $t_1 < \dots < t_k$. Row $j$ of the $n_i \times k$ matrix $p_i$ linearly interpolates the measurement time $t \in [t_r, t_{r+1}]$:

$$p_{ij} = \left(0_{r-1}^\top,\ \frac{t_{r+1} - t}{t_{r+1}-t_r},\ \frac{t - t_r}{t_{r+1} - t_r},\ 0_{k-r-1}^\top\right),$$

so each subject's covariance is $p_iDp_i^\top + \sigma^2 I_{n_i}$ with a single $k\times k$ matrix $D$ regardless of $n_i$ (Chung and Cho 2022, Eq. 1). $D$ is factored by the modified Cholesky decomposition $D = \Delta\Psi\Psi^\top\Delta$ for conjugate priors (Eq. 2).

**Theorem.** Writing $\tilde D = D - \hat D$ and $\tilde\sigma^2 = \sigma^2 - \hat\sigma^2$, the equations $P\,(I_n\otimes \tilde D)\,P^\top + \tilde\sigma^2 I_N = 0$ ($P = \operatorname{diag}(p_1,\dots,p_n)$) are equivalent to a linear system $AX = 0$ in the $\tfrac12 k(k+1) + 1$ unknowns $X = (\tilde d_{11}, \tilde d_{12}, \dots, \tilde d_{kk}, \tilde\sigma^2)$, where $A$ has $\tfrac12\sum_i n_i(n_i+1)$ rows determined by the interpolation weights (Lemma 1). The covariance parameters $(D, \sigma^2)$ are identifiable iff

$$\operatorname{rank}(A) = \tfrac12 k(k+1) + 1$$

(Theorem 1).

**Example.** With $k = 3$ grid points and every subject observed exactly at the grid times, $p_i = I_3$ and $\operatorname{rank}(A) = 6 < 7$: $\sigma^2$ is confounded with the diagonal of $D$. One additional measurement off the grid raises the rank to $7$ and restores identifiability; alternatively one sets $\sigma^2 = 0$ and models $D$ directly.

## Expansion

Two parameter values give the same marginal law of all $y_i$ iff their covariances coincide, i.e. iff $p_i\tilde Dp_i^\top + \tilde\sigma^2 I_{n_i} = 0$ for every $i$. Each entry $(j, j')$ of this matrix is linear in the entries of $\tilde D$ with coefficients $a_{ijr}a_{ij's}$, plus $\tilde\sigma^2$ on the diagonal, giving one row of $A$ per entry of the upper triangle. Identifiability is exactly triviality of the kernel. When all times are grid times, each diagonal equation reads $\tilde d_{rr} + \tilde\sigma^2 = 0$, so $(\tilde d_{rr}, \tilde\sigma^2) = (-s, s)$ is a nonzero solution.

## Sources

- W. Chung and Y. Cho, *Bayesian mixed models for longitudinal genetic data: theory, concepts, and simulation studies*, Genomics & Informatics 20(1) (2022), e8, Eqs. (1)–(2), Lemma 1 and Theorem 1. <https://doi.org/10.5808/gi.21080> (PMCID: PMC9001998)
