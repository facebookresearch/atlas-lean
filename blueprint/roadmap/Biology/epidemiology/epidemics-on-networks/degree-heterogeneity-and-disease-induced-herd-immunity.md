# Degree heterogeneity and disease-induced herd immunity in mean-field network SIR models

Let a population of size $N$ have degree distribution $P(k)$, with $N_k = P(k)N$ nodes of degree $k$, mean degree $\langle k\rangle$ and second moment $\langle k^2\rangle$. Let $\tau$ be the per-link transmission rate and $\gamma$ the recovery rate.

**Degree-based mean-field model.** With $[S_k], [I_k], [R_k]$ the numbers of degree-$k$ nodes in each state,

$$\dot{[S_k]} = -\tau k [S_k]\, \pi_I, \qquad \dot{[I_k]} = \tau k [S_k]\, \pi_I - \gamma [I_k], \qquad \dot{[R_k]} = \gamma [I_k], \qquad \pi_I = \frac{\sum_l l\, [I_l]}{\sum_l l\, N_l},$$

where $\pi_I$ is the probability that a random link end is infected. Its basic reproduction number is

$$R_0 = \frac{\tau \langle k^2\rangle}{\gamma \langle k\rangle}.$$

For the unclustered pairwise model, with pair-level closure, it is $R_0 = \tau(\langle k^2\rangle - \langle k\rangle)/((\tau + \gamma)\langle k\rangle)$.

**Residual reproduction number and herd immunity.** Linearizing the mean-field model about a state with susceptibles $[S_k]$ and no infection gives a rank-one next-generation operator. Its reproduction number is

$$R_{\mathrm{eff}} = \frac{\tau}{\gamma}\, \frac{\sum_k k^2 [S_k]}{\sum_k k\, N_k} = R_0\, \frac{\sum_k k^2 [S_k]}{\sum_k k^2 N_k}.$$

So a second wave cannot grow once $\sum_k k^2 [S_k] \le \sum_k k^2 N_k / R_0$. Infection removes susceptibles in proportion to $k$, so high-degree nodes leave the susceptible pool first. The $k^2$-weighted susceptible mass then falls faster than the unweighted fraction $\sum_k [S_k]/N$, and the disease-induced herd immunity level (the fraction ever infected when $R_{\mathrm{eff}}$ reaches $1$) is below the homogeneous value $1 - 1/R_0$. The gap widens with the variance of the degree distribution. The paper quantifies it numerically for negative-binomial degree distributions, $P(k) = \binom{k + n - 1}{n - 1} p^n (1-p)^k$, and for clustered, household and age-structured models.

## Depends on

- [$R_0$ under separable and preferential mixing](../next-generation-matrix-and-the-basic-reproductio/r0-under-separable-and-preferential-mixing.md)
- [Basic reproduction number of the next-generation matrix](../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

In the linearized model, a newly infected degree-$l$ node is infectious for mean time $1/\gamma$ and contributes $l/\sum_m m N_m$ to $\pi_I$. It therefore causes $\tau k [S_k]\, l / (\gamma \sum_m m N_m)$ infections among degree-$k$ nodes. This kernel factors as $a(k)\,b(l)$, so by the separable-mixing formula its only nonzero eigenvalue is $\sum_k b(k) a(k) = \tau \sum_k k^2 [S_k] / (\gamma \sum_m m N_m)$. Setting $[S_k] = N_k$ gives $R_0$.

## Sources

- F. Di Lauro, L. Berthouze, M. D. Dorey et al., *The impact of contact structure and mixing on control measures and disease-induced herd immunity in epidemic models: a mean-field model perspective*, Bull. Math. Biol. 83 (2021), 117, <https://doi.org/10.1007/s11538-021-00947-8>, PMCID PMC8518901, Section 2.1: Eq. (1) (negative-binomial degree distribution), Eq. (2) (degree-based mean-field model), Eqs. (6)–(7) ($R_0$ of the mean-field and pairwise models), and Section 3.1 (disease-induced herd immunity below $1 - 1/R_0$ under degree heterogeneity). The residual reproduction number is derived above.
