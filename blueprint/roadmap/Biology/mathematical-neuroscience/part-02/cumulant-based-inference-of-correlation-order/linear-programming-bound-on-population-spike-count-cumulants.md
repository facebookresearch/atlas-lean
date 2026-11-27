# Linear-programming bound on population spike-count cumulants

**Setting.** Model the summed activity of $N$ neurons by a compound Poisson process (CPP) with amplitude-$l$ event rates $\nu_l \ge 0$ ($l=1,\dots,N$), so that the population count $Z$ in a bin of width $h>0$ has cumulants

$$\kappa_i[Z] = h \sum_{l} l^{\,i}\,\nu_l, \qquad i \ge 1 .$$

A CPP has no cumulant correlations of order larger than $\xi$ iff $\nu_l = 0$ for all $l>\xi$ (see [the correlation-order theorem](correlation-order-of-a-compound-poisson-population-equals-its-maximal-amplitude.md)).

**Bound.** Let $Z'$ be an observed population count with cumulants $\kappa_1[Z'],\dots,\kappa_{m-1}[Z']$, $m \ge 2$, and fix $\xi \ge 1$. Define the linear program

$$\kappa_m^{*}(\xi) = \max\Bigl\{\, h\sum_{l=1}^{\xi} l^{m}\nu_l \;:\; \nu \in \mathbb{R}_{\ge 0}^{\xi},\; h\sum_{l=1}^{\xi} l^{\,i}\nu_l = \kappa_i[Z'] \text{ for } i=1,\dots,m-1 \Bigr\}.$$

If $Z'$ is the population count of a CPP without correlations of order $>\xi$, then the program is feasible and

$$\kappa_m[Z'] \le \kappa_m^{*}(\xi).$$

Consequently, evidence that $\kappa_m[Z'] > \kappa_m^{*}(\xi)$ implies correlations of order at least $\xi+1$.

**Case $m=2$.** The program has the closed form $\kappa_2^{*}(\xi) = \xi\,\kappa_1[Z']$ (put all mass on $l=\xi$, since $l^2 \le \xi l$ for $l \le \xi$). As $\kappa_2[Z]/\kappa_1[Z] = \mu_2[A]/\mu_1[A]$ is the population Fano factor, a population Fano factor larger than $\xi$ already forces correlations of order $>\xi$.

**Feasibility.** Because $\kappa_1 \le \kappa_2 \le \cdots$ for every CPP, the program can only be feasible for observed cumulants that are nondecreasing up to order $m-1$.

**CuBIC test.** For data $Z'_1,\dots,Z'_L$, replace $\kappa_i[Z']$ by the $k$-statistics $k_i$ ($i<m$), solve the program to obtain $\kappa_m^{*}(\xi)$ and a maximizing rate vector $\nu^{*}$, and test $H_0^{m,\xi}: \kappa_m[Z'] \le \kappa_m^{*}(\xi)$ with the statistic $k_m$, approximately normal with mean $\kappa_m^{*}(\xi)$ and with variance obtained from the cumulants of the maximizing CPP. Scanning $\xi = 1,2,\dots$ and $m = 2,3,\dots$, the largest $\xi$ for which $H_0^{m,\xi}$ is rejected gives the inferred lower bound $\xi+1$ on the order of correlation.

## Expansion

The cumulants of a CPP are linear in the rate vector, so "no correlation beyond order $\xi$" together with the lower-order cumulants fixed at their observed values defines a polytope of admissible rate vectors, and the $m$-th cumulant is a linear functional on it; its maximum is the largest $m$-th cumulant any such model can produce. The key reduction is from the $2^N-1$ subset rates to the $N$ amplitude rates: the population count depends only on the latter, which is why the test scales to hundreds of neurons and short recordings. The variance of $k_m$ under the null is obtained by assuming that the data come from the maximizing CPP, whose cumulants of all orders are known from the rate vector. Correlations among binned counts are insensitive to small jitter, so the bound targets near-coincident spiking at the resolution $h$.

## Depends on

- [Correlation order of a compound Poisson population equals its maximal amplitude](correlation-order-of-a-compound-poisson-population-equals-its-maximal-amplitude.md)

## Sources

- B. Staude, S. Rotter, S. Grün, "CuBIC: cumulant based inference of higher-order correlations in massively parallel spike trains", Journal of Computational Neuroscience (2010), Section 2.3 (Eq. (3)), Section 3.1–3.3 (Eqs. (4)–(10)), Section 4.2 (Eq. (11)), Appendix B (Eq. (25)), <https://doi.org/10.1007/s10827-009-0195-x>, PMCID PMC2940040.
