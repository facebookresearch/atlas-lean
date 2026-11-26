# Moments of the H-alpha index of Galton–Watson trees

**Setting.** Let $T$ be a Galton–Watson tree with offspring law $\xi$, $\mathbb P(\xi = 1) < 1$, and let $H_\alpha(T) = (1 - \sum_\ell p_\ell^\alpha)/(1 - 2^{1-\alpha})$ be its $H_\alpha$ balance index, $p_\ell$ the probability that the uniform random walk from the root ends at leaf $\ell$.

**Theorem.**
1. $\mathbb E[H_\alpha(T)] < \infty$ if and only if $\kappa_\alpha := \mathbb E\bigl[\xi^{1-\alpha} \mathbf 1_{\{\xi \ne 0\}}\bigr] < 1$, and then
$$\mathbb E[H_\alpha(T)] = \frac{1}{1 - 2^{1-\alpha}} \cdot \frac{\mathbb E\bigl[(1 - \xi^{1-\alpha})\mathbf 1_{\{\xi \ne 0\}}\bigr]}{1 - \kappa_\alpha}.$$
2. $\mathrm{Var}(H_\alpha(T)) < \infty$ if and only if $\kappa_\alpha < 1$ and $\mathbb E\bigl[\xi^{2(1-\alpha)}\mathbf 1_{\{\xi \ne 0\}}\bigr] < \infty$.
3. For every integer $m \ge 1$, $\mathbb E[H_\alpha(T)^m] < \infty$ if and only if $\kappa_\alpha < 1$ and $\mathbb E\bigl[\xi^{(1-\alpha)m}\mathbf 1_{\{\xi \ne 0\}}\bigr] < \infty$.

## Depends on

- [The H-alpha balance index of a phylogenetic network](h-alpha-balance-index.md)

## Expansion

By the grafting property, if the root has $k \ge 1$ children carrying independent copies $T_1, \dots, T_k$, then $H_\alpha(T) = c_k + k^{-\alpha} \sum_i H_\alpha(T_i)$ with $c_k = (1 - k^{1-\alpha})/(1 - 2^{1-\alpha})$. Taking expectations gives the linear fixed-point equation $\mu = \mathbb E[c_\xi \mathbf 1_{\xi \ne 0}] + \kappa_\alpha \mu$, solvable in $[0,\infty)$ exactly when $\kappa_\alpha < 1$. Higher moments satisfy similar recursions in which the new term $\mathbb E[\xi^{(1-\alpha)m}]$ appears through the $m$-th power of the factor $k^{1-\alpha}$. Markov branching trees satisfy analogous recurrences for the mean and variance.

## Sources

- F. Bienvenu, J.-J. Duchamps, H. Maffioli, "A parameterized family of balance indices for phylogenetic networks", arXiv:2606.24562 (2026), Theorem 2.1, Proposition 2.4, Corollary 2.5, Theorems 2.7 and 2.8, <https://doi.org/10.48550/arXiv.2606.24562>.
