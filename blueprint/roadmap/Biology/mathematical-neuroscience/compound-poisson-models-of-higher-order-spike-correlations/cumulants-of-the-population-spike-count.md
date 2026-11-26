# Cumulants of the population spike count

**Setting.** Let $X_1,\dots,X_N$ be the spike counts of $N$ neurons in a time bin of width $h$ and let $Z = \sum_{i=1}^N X_i$ be the population count, with $m$-th cumulant $\kappa_m[Z]$.

**Theorem 1.** $\kappa_m[Z]$ depends on the summed correlations (connected cumulants) among the $X_i$ of all orders $\le m$, and is independent of correlations of orders $> m$.

**Compound Poisson process.** Let a carrier Poisson process have rate $\nu$. At each carrier event, an amplitude $a \in \{1,\dots,N\}$ is drawn independently from an amplitude distribution $f_A$, and a spike is inserted simultaneously into $a$ of the $N$ processes $x_1(t),\dots,x_N(t)$; the population process is $z(t) = \sum_i x_i(t)$. Write $\mu_m = \sum_{a} a^m f_A(a)$ for the $m$-th moment of $f_A$.

**Theorem 2.** For a CPP with amplitude distribution $f_A$ and carrier rate $\nu$, and the counts $X_i$ obtained with bin width $h$,

$$\kappa_m[Z] = \mu_m\,\nu\,h \qquad (m \ge 1).$$

If $\xi \le N$ is the maximal correlation order, i.e. $f_A(a) = 0$ for $a > \xi$, and $\nu_a = \nu f_A(a)$ is the rate of events of amplitude $a$, then

$$\kappa_m[Z] = \sum_{a=1}^{\xi} a^m\,\nu_a\,h .$$

## Expansion

Theorem 1 follows from the multilinearity of cumulants: $\kappa_m[\sum_i X_i] = \sum_{i_1,\dots,i_m}\kappa[X_{i_1},\dots,X_{i_m}]$, a sum of joint cumulants of order exactly $m$ in which each term only sees the correlation structure of at most $m$ of the variables. For Theorem 2, $Z$ counts carrier events in the bin weighted by their amplitudes, so $Z$ is a compound Poisson variable with Poisson mean $\nu h$ and jump law $f_A$, whose cumulants are $\nu h\,\mathbb{E}[A^m]$. Because the counts are binned, the result does not depend on exact synchrony: jitter small relative to $h$ leaves the cumulants essentially unchanged. The CuBIC test exploits the linear system $\kappa_m[Z] = \sum_a a^m \nu_a h$ with $\nu_a \ge 0$: if the empirical cumulants up to order $m$ are incompatible with any nonnegative rates supported on $a \le \xi$, correlations of order greater than $\xi$ must be present. The cited paper extends this inference to non-stationary carrier rates.

## Sources

- B. Staude, S. Grün, S. Rotter, "Higher-order correlations in non-stationary parallel spike trains: statistical modeling and inference", Frontiers in Computational Neuroscience 4 (2010) 16, Theorems 1–2, Eqs. (3)–(4), <https://doi.org/10.3389/fncom.2010.00016>, PMCID PMC2906200.
