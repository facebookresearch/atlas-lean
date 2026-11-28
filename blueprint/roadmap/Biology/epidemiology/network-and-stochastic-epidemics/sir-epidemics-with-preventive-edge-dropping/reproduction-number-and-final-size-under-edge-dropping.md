# Reproduction number and final size under preventive edge dropping

**Model.** Individuals form a configuration-model network on $N$ vertices whose degree $D$ has distribution $(p_k)$, mean $\mu_D$, variance $\sigma_D^2$, bounded support and probability generating function $f_D(s) = \sum_k p_k s^k$. An infectious individual infects each susceptible neighbour at rate $\beta$ along their shared edge and recovers at rate $\gamma$; each susceptible drops each edge to an infectious neighbour at rate $\omega$, independently. Initially a vanishing fraction is infectious and all others susceptible.

**Basic reproduction number (2.1).**

$$R_0 = \frac{\beta}{\beta + \gamma + \omega}\left(\mu_D + \frac{\sigma_D^2}{\mu_D} - 1\right).$$

The first factor is the probability that an infective transmits across a given edge before it recovers or the neighbour drops the edge; the second is the mean excess degree $\mathbb{E}[\tilde D] - 1$ of the size-biased neighbour degree $P(\tilde D = k) = k p_k / \mu_D$. $R_0$ is strictly decreasing in $\omega$.

**Final size (Proposition 5.1(b)).** If $R_0 > 1$, the fraction ultimately infected in the large-population deterministic limit of a major outbreak is

$$\rho = 1 - f_D(s), \qquad (\beta + \omega + \gamma)\, s - (\omega + \gamma) = \frac{\beta}{\mu_D} f_D'(s),$$

where $s$ is the unique solution in $[0, 1)$.

**Equivalence with increased recovery (Remark 5.3).** The law-of-large-numbers limit of the susceptible process (classified by effective degree), and therefore $R_0$, the Malthusian growth rate and $\rho$, depend on $(\gamma, \omega)$ only through $\gamma + \omega$: they coincide with those of the standard Markov SIR epidemic on the same network without dropping and with recovery rate $\gamma + \omega$. The infective process and the central-limit fluctuations differ between the two models.

## Expansion

Track $\theta(t)$, the probability that a given edge has not transmitted infection to a fixed susceptible endpoint. Along an edge to an infectious neighbour, transmission competes with recovery and dropping, and both recovery and dropping simply end the edge's capacity to transmit, so $\theta$ obeys $\dot\theta = \beta f_D'(\theta)/\mu_D - (\beta + \gamma + \omega)\theta + \gamma + \omega$ (Equation 5.21) with $\theta(0) = 1$; $\gamma$ and $\omega$ enter only as a sum. A susceptible of degree $k$ escapes infection with probability $\theta^k$, giving $1 - f_D(\theta(\infty))$ for the final size, and $\theta(\infty)$ solves the fixed-point equation above; convexity of $f_D'$ gives uniqueness in $[0, 1)$ when $R_0 > 1$. Laws of large numbers and functional central limit theorems for the full process follow from an effective-degree formulation and the theory of density-dependent population processes, for both the Molloy–Reed and Newman–Strogatz–Watts versions of the configuration model.

## Sources

- F. Ball, T. Britton, K. Y. Leung, D. Sirl, "A stochastic SIR network epidemic model with preventive dropping of edges", Journal of Mathematical Biology 78 (2019) 1875–1951, Equations (2.1), (5.21), (5.28)–(5.31), Proposition 5.1, Remark 5.3, <https://doi.org/10.1007/s00285-019-01329-4> (PMC6469721).
