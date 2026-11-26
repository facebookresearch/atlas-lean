# Spectral independence implies polynomial mixing of Glauber dynamics

Let $\mu$ be an $\eta$-spectrally independent distribution on $\{0,1\}^n$ with $\eta \ge 0$ constant. Then the Glauber dynamics (single-site heat-bath) for $\mu$ has spectral gap at least $\Omega_\eta\bigl(n^{-1-\eta}\bigr)$, hence mixes in polynomial time $n^{O(1+\eta)}$ from a warm start. Applied to the hardcore model on graphs of maximum degree $\Delta$ at fugacity strictly below the uniqueness threshold $\lambda_c(\Delta) = (\Delta-1)^{\Delta-1}/(\Delta-2)^{\Delta}$, this gives polynomial-time approximate sampling and counting.

## Proof sketch

Glauber dynamics on $\mu$ is the down-up walk on the top faces of the literal complex of $\mu$. Spectral independence bounds the second eigenvalue of every link of a $j$-face by $\eta/(n-j-2)$, and the Alev–Lau product $\prod_{j}(1 - \eta/(n-j-2))$ is $\Omega(n^{-\eta})$. Below the uniqueness threshold, correlation decay on the self-avoiding walk tree bounds the maximum eigenvalue of the influence matrix by a constant depending only on the gap to $\lambda_c(\Delta)$.

## Depends on

- [Spectral independence of a distribution on the hypercube](spectral-independence.md)
- [Alev–Lau local-to-global bound for the down-up walk](alev-lau-local-to-global.md)

## Proof depends on

- [Spectral independence of a distribution on the hypercube](spectral-independence.md)
- [Alev–Lau local-to-global bound for the down-up walk](alev-lau-local-to-global.md)

## Sources

- N. Anari, K. Liu, S. Oveis Gharan, "Spectral independence in high-dimensional expanders and applications to the hardcore model", FOCS (2020), arXiv:2001.00303.
- V. L. Alev, L. C. Lau, "Improved analysis of higher order random walks and applications", STOC (2020), arXiv:2001.02827.
