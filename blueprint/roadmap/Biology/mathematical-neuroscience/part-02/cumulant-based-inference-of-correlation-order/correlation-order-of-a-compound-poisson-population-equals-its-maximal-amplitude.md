# Correlation order of a compound Poisson population equals its maximal amplitude

**Model.** Let $x_1(t),\dots,x_N(t)$ be spike trains generated as follows. For every nonempty subset $M \subseteq \{1,\dots,N\}$ let $y'_M(t)$ be a stationary Poisson process of rate $\nu'_M \ge 0$, all independent; at each event of $y'_M$ every neuron $i \in M$ fires one spike. The superposition $z(t)=\sum_i x_i(t)$ is then a compound Poisson process (CPP): its events form a Poisson process of carrier rate $\nu=\sum_M \nu'_M$, and each event carries an i.i.d. amplitude $A$ (the number of neurons firing together) with amplitude distribution

$$f_A(l) = \frac{1}{\nu}\sum_{|M| = l} \nu'_M, \qquad l = 1,\dots,N .$$

Fix a bin width $h>0$ and let $X=(X_1,\dots,X_N)$ be the spike counts of the $N$ neurons in one bin, and $Z=\sum_i X_i$ the population count.

**Correlation order.** For a multi-index $J \in \mathbb{N}^N$ let $n_J$ be the number of its nonzero entries and $\kappa_J[X]$ the corresponding mixed cumulant, i.e. the coefficient of $(iu)^J/J!$ in $\log \mathbb{E}\,e^{i u\cdot X}$. The components of $X$ have *correlations of order $m$* if $\kappa_J[X] \neq 0$ for some $J$ with $n_J = m$.

**Theorem.** The components of $X$ have correlations of order $m$ if and only if $f_A$ assigns positive probability to some amplitude $\ge m$, i.e. iff $\nu'_M>0$ for some $M$ with $|M| \ge m$.

**Corollaries.**
1. The population count is compound Poisson with

$$\kappa_m[Z] = \nu\,h\,\mu_m[A] = h\sum_{l=1}^{N} l^m\,\nu_l, \qquad \nu_l = \nu f_A(l),$$

so $\kappa_1[Z] \le \kappa_2[Z] \le \kappa_3[Z] \le \cdots$, since the moments of a positive integer variable are nondecreasing in the order.
2. Events of amplitude $\xi$ create correlations of every order $\le \xi$; correlations of order exactly $m$ cannot be present without those of all lower orders, and the CPP produces only nonnegative cumulant correlations.
3. The correlation order does not depend on $h$: it is a property of the injected coincidences, not of the binning.

## Expansion

Write $X = \sum_M \delta_M Y'_M$, where $\delta_M \in \{0,1\}^N$ is the indicator vector of $M$ and $Y'_M$ is the (Poisson, mean $\nu'_M h$) count of $y'_M$ in the bin. By independence the mixed cumulants add over $M$. A mixed cumulant of the vector $\delta_M Y'_M$ vanishes unless $\operatorname{supp}(J) \subseteq M$ (otherwise one argument is the constant $0$), and when $\operatorname{supp}(J) \subseteq M$ it equals a univariate cumulant of the Poisson variable $Y'_M$, which is $\nu'_M h$ for every order. Hence

$$\kappa_J[X] = h \sum_{M \supseteq \operatorname{supp}(J)} \nu'_M .$$

Since all rates are nonnegative, $\kappa_J[X]\neq 0$ iff some $M \supseteq \operatorname{supp}(J)$ has $\nu'_M>0$, and a $J$ with $n_J=m$ exists with this property iff some $M$ with $|M|\ge m$ has positive rate. Corollary 1 follows by setting all arguments of the multivariate cumulant generating function equal: the amplitude-$l$ events form independent Poisson processes of rates $\nu_l$, and $Z = \sum_l l\,Y_l$ with $Y_l$ Poisson of mean $\nu_l h$. Spikes copied with a jitter small relative to $h$ leave the counting correlations essentially unchanged.

## Sources

- B. Staude, S. Rotter, S. Grün, "CuBIC: cumulant based inference of higher-order correlations in massively parallel spike trains", Journal of Computational Neuroscience (2010), Section 2.2–2.4 (Eq. (3), Theorem 1), Appendix A (Definition 1 and proof of Theorem 1), <https://doi.org/10.1007/s10827-009-0195-x>, PMCID PMC2940040.
