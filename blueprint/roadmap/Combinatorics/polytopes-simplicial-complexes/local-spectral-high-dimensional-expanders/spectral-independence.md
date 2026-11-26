# Spectral independence of a distribution on the hypercube

Let $\mu$ be a probability distribution on $\{0,1\}^n$ (or on $[q]^n$). For a pinning $\tau$ of a subset of coordinates, the **signed pairwise influence matrix** $\Psi^{\tau}_{\mu}$ is indexed by pairs of unpinned literals $(i, a), (j, b)$ with

$$
\Psi^{\tau}_{\mu}\bigl((i,a),(j,b)\bigr) = \Pr_{\mu}\bigl[x_j = b \mid x_i = a,\ \tau\bigr] - \Pr_{\mu}\bigl[x_j = b \mid \tau\bigr]
$$

for $i \ne j$, and $0$ when $i = j$. The distribution is **$\eta$-spectrally independent** if $\lambda_{\max}(\Psi^{\tau}_\mu) \le \eta$ for every pinning $\tau$. Equivalently, the simplicial complex whose top faces are the supports of $\mu$ viewed as sets of literals, weighted by $\mu$, has every link of a $j$-face with second eigenvalue at most $\eta/(n-j-2)$.

## Depends on

- [Local spectral expanders (one-sided and two-sided)](local-spectral-expander.md)

## Sources

- N. Anari, K. Liu, S. Oveis Gharan, "Spectral independence in high-dimensional expanders and applications to the hardcore model", FOCS (2020), arXiv:2001.00303.
- V. L. Alev, L. C. Lau, "Improved analysis of higher order random walks and applications", STOC (2020), arXiv:2001.02827.
