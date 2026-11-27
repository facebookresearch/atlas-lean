# Gompertz waiting times under exponential growth

Consider a variable-size Cannings model whose fixed-size coalescence probability satisfies $c_N = c N^{-\gamma} + o(N^{-\gamma})$ for constants $c, \gamma > 0$, with exponential growth on the coalescent time scale: $\nu(t) = e^{-\rho t}$ for $\rho > 0$, corresponding to sizes $N_{r-1} = \lfloor N_r (1 - c_N \rho) \rfloor$. Then the time change of the limiting Λ-coalescent is (Cor. 3, Eq. 10)

$$G(t) = \int_0^t e^{\rho \gamma s}\, ds = \frac{e^{\rho \gamma t} - 1}{\rho \gamma}.$$

Consequently the waiting time $T$ to the next merger, given that the last merger occurred at time $t_0$ and left $b$ lineages, is Gompertz distributed:

$$\mathbb P_{t_0}(T \le t) = 1 - \exp\!\Big( - \frac{\lambda_b\, e^{\rho \gamma t_0}}{\rho \gamma} \big(e^{\rho \gamma t} - 1\big) \Big), \qquad t \ge 0,$$

where $\lambda_b$ is the total merger rate of the Λ-coalescent with $b$ blocks.

## Depends on

- [Time-changed Λ-coalescent limits of variable-size Cannings models](time-changed-lambda-coalescent-limits.md)
- [Total merger rate of a Λ-coalescent](../../coalescents/total-merger-rate.md)

## Expansion

With $\nu(s) = e^{-\rho s}$ we get $\nu(s)^{-\gamma} = e^{\rho \gamma s}$, which integrates to the stated $G$. In the time-changed process $\Pi_{G(t)}$ a configuration with $b$ blocks jumps at rate $\lambda_b G'(t) = \lambda_b e^{\rho \gamma t}$, so the survival function of the next jump after $t_0$ is $\exp\big(-\lambda_b (G(t_0 + t) - G(t_0))\big)$, which is the Gompertz law above. For Kingman's coalescent ($\gamma = 1$, $\lambda_b = \binom{b}{2}$) this reduces to the classical coalescent with exponential growth.

## Sources

- F. Freund, *Cannings models, population size changes and multiple-merger coalescents*, J. Math. Biol. (2020). <https://doi.org/10.1007/s00285-020-01470-5> (PMCID: PMC7052052)
