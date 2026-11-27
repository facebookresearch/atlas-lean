# Superposition of single-index-case branching epidemics

Consider an age-dependent branching process for an outbreak without susceptible depletion: every case independently produces a number of secondary cases with the negative-binomial law of mean $R_0 \ge 0$ and dispersion $k > 0$, and each secondary case is infected after an independent generation interval drawn from a fixed law on $(0, \infty)$ (for example, gamma with shape 2 and mean $D$). Let $C(t)$ be the cumulative number of cases by time $t$ in the epidemic started by one index case at time 0.

If $n$ index cases are introduced at times $T_1, \dots, T_n$, independent of the transmission process, then the cumulative incidence of the combined epidemic has the law of

$$C^{(n)}(t) = \sum_{i=1}^n C_i(t - T_i), \qquad C_i(u) = 0 \text{ for } u < 0,$$

where $C_1, C_2, \dots$ are independent copies of $C$, independent of $(T_i)$. In particular:

1. The number of secondary cases produced by the $n$ index cases is negative binomial with mean $n R_0$ and dispersion $n k$.
2. The combined epidemic goes extinct with probability $q^n$, where $q$ is the least $s \in [0, 1]$ with $(1 + (R_0/k)(1 - s))^{-k} = s$.

## Depends on

- [Negative-binomial offspring distribution](../../superspreading-and-negative-binomial-offspring/nb-offspring.md)
- [Negative-binomial extinction probability is the least fixed point](../../superspreading-and-negative-binomial-offspring/is-least-extinction-prob-nb-offspring.md)

## Proof sketch

Without depletion, the offspring numbers and generation intervals of each case are independent of everything else, so the descendants of different index cases form independent subtrees, and shifting each subtree by its introduction time gives the sum. The negative-binomial law with mean $R_0$ and dispersion $k$ has generating function $(1 + (R_0/k)(1 - s))^{-k}$; the $n$-th power is the generating function with mean $n R_0$ and dispersion $n k$. The combined epidemic dies out exactly when every subtree does, which gives $q^n$. The superposition is what makes large simulation studies cheap: one library of single-index-case epidemics can be resampled and time-shifted to build epidemics with any number of index cases and any introduction dates, as was done to infer early SARS-CoV-2 transmission from the epidemic size in Wuhan.

## Sources

- J. Riou and C. L. Althaus, "Pattern of early human-to-human transmission of Wuhan 2019 novel coronavirus (2019-nCoV), December 2019 to January 2020", Eurosurveillance 25(4) (2020), 2000058, section "Simulating early outbreak trajectories", <https://doi.org/10.2807/1560-7917.ES.2020.25.4.2000058>, PMCID: PMC7001239.
