# Hybrid reward–punishment incentives and the cooperation threshold

**Model.** A well-mixed population of $N \ge 2$ players, each a cooperator (C) or defector (D), plays a cooperation dilemma; with $j$ cooperators let $\Pi_C(j), \Pi_D(j)$ be the average payoffs and $\delta = \Pi_C(j) - \Pi_D(j)$. For the donation game (benefit $B >$ cost $c$) and the public goods game (group size $n$, multiplier $1 < r < n$, contribution $c$),
$$\delta_{\mathrm{DG}} = -\Big(c + \frac{B}{N-1}\Big), \qquad \delta_{\mathrm{PGG}} = -c\Big(1 - \frac{r(N-n)}{n(N-1)}\Big),$$
both negative and independent of $j$. An institution raises each cooperator's payoff by $\theta$ at cost $\theta/a$ (reward) or lowers each defector's payoff by $\theta$ at cost $\theta/b$ (punishment), with efficiency ratios $a, b > 0$; the **hybrid** scheme pays $\theta\min(j/a, (N-j)/b)$ per generation. Strategies update by the pairwise-comparison (Fermi) rule with selection intensity $\beta > 0$, giving a birth–death chain on $\{0, \dots, N\}$ with transitions $u_{i,i\pm1} = \frac{N-i}{N}\frac{i}{N}\big(1 + e^{\mp\beta(\delta + \theta)}\big)^{-1}$ and absorbing states $0, N$. With fundamental matrix $(n_{ik}) = (I-U)^{-1}$ on the transient states and a mutant equally likely to arise in either monomorphic state, the expected total costs are
$$E_{\mathrm{mix}}(\theta) = \frac{\theta}{2}\sum_{j=1}^{N-1}(n_{1j} + n_{N-1,j})\min\Big(\frac{j}{a}, \frac{N-j}{b}\Big),$$
and $E_r$, $E_p$ with $j/a$, respectively $(N-j)/b$, in place of the minimum.

**Proposition (cooperation threshold).** The ratio of fixation probabilities of a single cooperator and a single defector is
$$\frac{\rho_{D,C}}{\rho_{C,D}} = e^{\beta(N-1)(\delta + \theta)},$$
so the long-run frequency of cooperation $\rho_{D,C}/(\rho_{D,C} + \rho_{C,D})$ is at least $\omega \in (0,1)$ if and only if
$$\theta \ge \theta_0(\omega) = \frac{1}{(N-1)\beta}\log\frac{\omega}{1-\omega} - \delta .$$
The design problem is to minimize $E_{\mathrm{mix}}(\theta)$ over $\theta \ge \theta_0(\omega)$.

**Proposition (hybrid incentives are cheaper).** For all $\theta$, $E_{\mathrm{mix}}(\theta) \le \min\{E_r(\theta), E_p(\theta)\}$. If $b/a \le 1/(N-1)$ then $E_{\mathrm{mix}} = E_r$ (pure reward is optimal), and if $b/a \ge N-1$ then $E_{\mathrm{mix}} = E_p$ (pure punishment is optimal); in between the hybrid scheme is strictly cheaper.

## Depends on

- [Moran Fixation](../isothermal-theorem-for-evolutionary-graph-dynami/moran-fixation.md)
- [Rest point of the replicator equation](../replicator-dynamics/is-rest-point.md)

## Expansion

For a birth–death chain, $\rho_{D,C}/\rho_{C,D} = \prod_{k=1}^{N-1} u_{k,k-1}/u_{k,k+1}$, and each factor is $(1 + e^{\beta(\delta+\theta)})/(1 + e^{-\beta(\delta+\theta)}) = e^{\beta(\delta+\theta)}$; requiring $e^{\beta(N-1)(\delta+\theta)} \ge \omega/(1-\omega)$ gives $\theta_0$. The cost comparison is termwise: $\min(j/a, (N-j)/b)$ is at most each argument. The minimum equals $j/a$ for every $j \le N-1$ iff it does at $j = N-1$, i.e. $(N-1)/a \le 1/b$, and symmetrically for punishment. The hybrid scheme requires the institution to observe the current number of cooperators.

## Sources

- M. H. Duong, C. M. Durbac and T. A. Han, "Cost optimisation of hybrid institutional incentives for promoting cooperation in finite populations", Journal of Mathematical Biology 87 (2023), Section 2, Equations (1)–(7) and Proposition 1, <https://doi.org/10.1007/s00285-023-02011-6> (PMC10603005).
