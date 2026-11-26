# Logistic arrival time of the n-th sequential mutant

In the [sequential-mutation birth–death process](mittag-leffler-limit-of-sequential-mutant-populations.md) (type-$n$ division, death and mutation rates $\alpha_n,\beta_n,\nu_n$; net rates $\lambda_n=\alpha_n-\beta_n$ with $\lambda_1>0$; running-max fitness $\delta_n$ attained $r_n$ times; scale parameters $\omega_n$), let $\tau_{n+1}$ be the time at which the first type-$(n+1)$ cell appears. For small mutation rates (ordered limit $\nu_1\to0,\dots,\nu_n\to0$),

$$\mathbb P(\tau_{n+1}>t)\approx\Big[1+\exp\big(\lambda_1\,(t-t_{1/2}(n+1))\big)\Big]^{-1},$$

a logistic law with scale $\lambda_1^{-1}$, so its variance is approximately $\pi^2/(3\lambda_1^2)$ for every $n$, and its median (equal to its mean) is

$$t_{1/2}(n+1)=\frac{1}{\delta_n}\log\frac{\delta_n}{\omega_n\,\nu_n\,\big[\delta_n^{-1}\log(\nu_n^{-1})\big]^{r_n-1}}.$$

For $n=1$ this gives $t_{1/2}(2)=\lambda_1^{-1}\log\big(\lambda_1^2/(\alpha_1\nu_1)\big)$. For the first type-$(n+1)$ cell whose lineage survives (possible only if $\lambda_{n+1}>0$), the same holds with $\nu_n$ replaced by $\nu_n\lambda_{n+1}/\alpha_{n+1}$.

The shape of the arrival-time distribution depends only on the type-1 growth rate; mutation rates and later fitnesses only shift its centre. Consequently, waiting times can be treated as deterministic once $t_{1/2}(n+1)\gg\pi/(\sqrt3\,\lambda_1)$, and fluctuations of arrival times cannot discriminate between paths needing different numbers of mutations.

## Depends on

- [Mittag-Leffler limit of sequential mutant populations](mittag-leffler-limit-of-sequential-mutant-populations.md)

## Expansion

Type-$(n+1)$ cells are created at rate $\nu_nZ_n(t)\approx\nu_nV_nt^{r_n-1}e^{\delta_nt}$, so conditionally on $V_n$ the survival function is $\exp\big(-\nu_nV_n\int^tt'^{\,r_n-1}e^{\delta_nt'}dt'\big)$. Averaging over $V_n$ means evaluating the Laplace transform of the Mittag-Leffler law, $(1+(\omega_n s)^{\lambda_1/\delta_n})^{-1}$, at $s\propto\nu_n t^{r_n-1}e^{\delta_nt}/\delta_n$; since $(e^{\delta_nt})^{\lambda_1/\delta_n}=e^{\lambda_1t}$, the result is $1/(1+e^{\lambda_1(t-t_{1/2})})$ to leading order, with $t_{1/2}$ the time at which $\omega_n\nu_nt^{r_n-1}e^{\delta_nt}/\delta_n=1$. Replacing $t^{r_n-1}$ by $(\delta_n^{-1}\log\nu_n^{-1})^{r_n-1}$ at that time gives the stated median.

## Sources

- M. D. Nicholson, D. Cheek, T. Antal, "Sequential mutations in exponentially growing populations", PLoS Computational Biology (2023), Results Eqs. (4)–(6) and the arrival-time discussion; Methods, Proposition 4, Corollary 3 and Theorem 2, <https://doi.org/10.1371/journal.pcbi.1011289>, PMCID PMC10359018.
