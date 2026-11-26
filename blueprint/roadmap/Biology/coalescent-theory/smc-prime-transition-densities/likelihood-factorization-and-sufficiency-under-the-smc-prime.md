# Likelihood factorization and sufficiency under the SMC$'$

Let the observed data from a chromosomal segment of length $L$ be the sequence of local genealogies and the breakpoints at which they change,

$$Y = \{(g_0, 0), (g_1, b_1), \dots, (g_{m-1}, b_{m-1}),\, s_m = L - b_{m-1}\},$$

including both visible and invisible events. Under the SMC$'$ with recombination rate $\rho$ per site and effective size trajectory $N(t)$ the observed-data likelihood factors as

$$\mathcal L_{\mathrm{obs}}(Y; N(t), \rho) = \underbrace{\Pr[g_0 \mid N(t)] \prod_{i=0}^{m-2} \Pr[g_{i+1} \mid g_i, N(t)]}_{\text{depends on } N(t)} \times \underbrace{h(L - b_{m-1} \mid g_{m-1}, \rho) \prod_{i=0}^{m-2} f(s_{i+1} \mid g_i, \rho)}_{\text{depends on } \rho},$$

where $f(s \mid g, \rho) = \rho \ell\, e^{-\rho \ell s}$ and $h$ is the corresponding survival function. Two consequences follow by the factorization theorem. First, the total tree lengths $\ell_0, \dots, \ell_{m-1}$ together with the locus lengths $s_1, \dots, s_{m-1}, L - b_{m-1}$ are sufficient for $\rho$. Second, the breakpoint positions $b_0, \dots, b_{m-1}$ carry no information about $N(t)$; the sequence of local genealogies alone does.

## Depends on

- [Marginal visible transition density under the SMC$'$](marginal-visible-transition-density-under-the-smc-prime.md)
- [Invisible transitions of the SMC$'$ and the $F$ matrix](invisible-transition-probability-and-f-matrices.md)

## Expansion

The factorization is immediate from the conditional independence of the embedded chain: given the current genealogy, the distance to the next breakpoint depends only on the total tree length and $\rho$, while the next genealogy depends only on the current one and $N(t)$. Combining this with the $F$-matrix representation of the transition densities shows that the sequence of local *Tajima's* genealogies — ranked tree shapes together with coalescence times — is sufficient for $N(t)$ under the SMC$'$, so inference can integrate over a state space of Euler zigzag size rather than over labelled topologies: for $n = 10$ there are $7{,}936$ ranked tree shapes against $2{,}571{,}912{,}000$ labelled topologies. Placing a log-Gaussian process prior on $N(t)$, with Brownian motion giving a sparse inverse covariance and a Gamma prior on its precision, then yields a nonparametric posterior for the whole trajectory rather than a piecewise-constant point estimate on a user-chosen time grid.

## Sources

- J. A. Palacios, J. Wakeley, S. Ramachandran, "Bayesian nonparametric inference of population size changes from sequential genealogies", *Genetics* 201 (2015), 281–304, <https://doi.org/10.1534/genetics.115.177980> (PMC4566269). Methods: SMC$'$ calculations, Equations (12)–(16), and "Sequential Tajima's genealogies are sufficient statistics under the SMC$'$".
