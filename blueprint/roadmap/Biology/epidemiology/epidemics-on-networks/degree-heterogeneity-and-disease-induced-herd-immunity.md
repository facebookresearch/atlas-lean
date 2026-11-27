# Degree heterogeneity and disease-induced herd immunity in mean-field network SIR models

Let a population of size $N$ have degree distribution $P(k)$, with $N_k = P(k)N$ nodes of degree $k$, mean degree $\langle k\rangle$ and second moment $\langle k^2\rangle$. Let $\tau$ be the per-link transmission rate and $\gamma$ the recovery rate.

**Degree-based mean-field model.** With $[S_k], [I_k], [R_k]$ the numbers of degree-$k$ nodes in each state,

$$\dot{[S_k]} = -\tau k [S_k]\, \pi_I, \qquad \dot{[I_k]} = \tau k [S_k]\, \pi_I - \gamma [I_k], \qquad \dot{[R_k]} = \gamma [I_k], \qquad \pi_I = \frac{\sum_l l\, [I_l]}{\sum_l l\, N_l},$$

where $\pi_I$ is the probability that a random link end is infected. Its basic reproduction number is

$$R_0 = \frac{\tau \langle k^2\rangle}{\gamma \langle k\rangle}.$$

For the unclustered pairwise model, with pair-level closure, it is $R_0 = \tau(\langle k^2\rangle - \langle k\rangle)/((\tau + \gamma)\langle k\rangle)$.

**Residual reproduction number and herd immunity.** Linearizing the mean-field model about a state with susceptibles $[S_k]$ and no infection gives a rank-one next-generation operator. Its reproduction number is

$$R_{\mathrm{eff}} = \frac{\tau}{\gamma}\, \frac{\sum_k k^2 [S_k]}{\sum_k k\, N_k} = R_0\, \frac{\sum_k k^2 [S_k]}{\sum_k k^2 N_k}.$$

So a second wave cannot grow once $\sum_k k^2 [S_k] \le \sum_k k^2 N_k / R_0$. For an epidemic started from a vanishing seed in a fully susceptible population, the model gives $[S_k] = N_k\, \theta(t)^k$ at time $t$, with $\theta(t) = \exp\big(-\tau \int_0^t \pi_I\big) \in (0, 1]$, so infection removes high-degree susceptibles first. If $R_0 > 1$ and $R_{\mathrm{eff}}$ reaches $1$ at $\theta^* \in (0, 1)$, the disease-induced herd immunity level (the fraction ever infected at that moment) satisfies

$$1 - \sum_k P(k)\, (\theta^*)^k \le 1 - \frac{1}{R_0},$$

with equality only when all nodes have the same degree. The same holds if $\tau$ is multiplied by a time-dependent control factor, as in the paper's lockdown scenarios, since $[S_k]$ keeps the form $N_k\theta^k$. The paper computes the disease-induced herd immunity level numerically, as the cumulative incidence at the end of an optimally scaled lockdown after which the epidemic is subcritical, for shifted negative-binomial degree distributions $P(k) = \binom{k - s + n - 1}{n - 1} p^n (1-p)^{k - s}$, $k \ge s$, with mean degree $10$ and shifts chosen to avoid degree zero that differ between the distributions compared: $s = 9$ for the delta-like law (variance $1$) and $s = 1$ for the normal-like and scale-free-like laws (variances $30$ and $300$) (Table 1), and for clustered, household and age-structured models. In those examples the level decreases from the delta-like to the scale-free-like law (Section 3.1, Fig. 3); this is an observation for the distributions and settings studied, not an ordering by variance alone, since the threshold depends on the whole $k^2$-weighted law of the remaining susceptibles.

## Depends on

- [The basic reproduction ratio `R₀`](../next-generation-operator-and-basic-reproduction/generation-growth.md)

## Proof depends on

- [`R₀` for a separable kernel](../next-generation-operator-and-basic-reproduction/generation-growth-eq-integral-of-separab.md)

## Expansion

In the linearized model, a newly infected degree-$l$ node is infectious for mean time $1/\gamma$ and contributes $l/\sum_m m N_m$ to $\pi_I$. It therefore causes $\tau k [S_k]\, l / (\gamma \sum_m m N_m)$ infections among degree-$k$ nodes. This kernel factors as $a(k)\,b(l)$, so by the separable-mixing formula the spectral radius is $\sum_k b(k) a(k) = \tau \sum_k k^2 [S_k] / (\gamma \sum_m m N_m)$. Setting $[S_k] = N_k$ gives $R_0$. Integrating $\dot{[S_k]} = -\tau k [S_k]\pi_I$ gives $[S_k] = N_k\theta^k$. At the threshold, $\sum_k k^2 P(k) (\theta^*)^k / \sum_k k^2 P(k) = 1/R_0$; since $k \mapsto k^2$ is nondecreasing and $k \mapsto (\theta^*)^k$ is decreasing, Chebyshev's sum inequality gives $\sum_k k^2 P(k)(\theta^*)^k \le \sum_k k^2 P(k) \cdot \sum_k P(k)(\theta^*)^k$, with equality only for a one-point degree law. Hence $\sum_k P(k)(\theta^*)^k \ge 1/R_0$.

## Sources

- F. Di Lauro, L. Berthouze, M. D. Dorey et al., *The impact of contact structure and mixing on control measures and disease-induced herd immunity in epidemic models: a mean-field model perspective*, Bull. Math. Biol. 83 (2021), 117, <https://doi.org/10.1007/s11538-021-00947-8>, PMCID PMC8518901, Section 2.1: Eq. (1) (negative-binomial degree distribution) and Table 1 (the shifted distributions used), Eq. (2) (degree-based mean-field model), Eqs. (6)–(7) ($R_0$ of the mean-field and pairwise models), and Section 3.1 with Fig. 3 (numerical disease-induced herd immunity levels). The residual reproduction number and the comparison with $1 - 1/R_0$ are derived above.
