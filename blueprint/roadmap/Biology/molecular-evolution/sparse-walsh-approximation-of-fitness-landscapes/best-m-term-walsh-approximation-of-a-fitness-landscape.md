# Best m-term Walsh approximation of a fitness landscape

**Setting.** With $\vec W \in \mathbb{R}^{2^L}$, the Hadamard matrix $\Psi$ and the epistatic coefficients $\vec E_W = 2^{-L}\Psi\vec W$ as in the [Parseval identity for Walsh epistasis coefficients](parseval-identity-for-walsh-epistasis-coefficients.md), a *subsetting approximation* with $m$ terms ($0 \le m \le 2^L$) is $\vec W^{(m)} = \Psi \vec E_{W^{(m)}}$, where $\vec E_{W^{(m)}}$ agrees with $\vec E_W$ on $m$ chosen coordinates and is zero on the remaining $2^L - m$.

**Theorem.** Among all subsetting approximations with $m$ terms, the sum of squares $\|\vec W - \vec W^{(m)}\|^2$ is minimized exactly when $\vec E_{W^{(m)}}$ keeps the $m$ components of $\vec E_W$ that are largest in absolute value. The minimum equals $2^L$ times the sum of squares of the discarded coefficients.

In particular, truncating a landscape to all interactions of order at most $k$ is least-squares optimal only if those are the largest coefficients; dropping a large higher-order coefficient can change the landscape's peaks and sign-epistasis structure.

## Depends on

- [Parseval identity for Walsh epistasis coefficients](parseval-identity-for-walsh-epistasis-coefficients.md)

## Expansion

By the Parseval identity, $\|\vec W - \vec W^{(m)}\|^2 = 2^L \|\vec E_W - \vec E_{W^{(m)}}\|^2 = 2^L \sum_{h \notin S} (E_W)_h^2$, where $S$ is the kept index set. This is minimized by keeping the $m$ coefficients of largest absolute value; the sign of a coefficient plays no role.

## Sources

- D. M. Weinreich, Y. Lan, J. Jaffe and R. B. Heckendorn, "The Influence of Higher-Order Epistasis on Biological Fitness Landscape Topography", *Journal of Statistical Physics* (2018), Sect. 2.3 (subsetting approximations) and Appendix, Theorem 2. <https://doi.org/10.1007/s10955-018-1975-3> (PMC5986866)
