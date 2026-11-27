# Conditional Monte Carlo estimator of reaction-network distributions

**Setting.** A stochastic reaction network with $d$ species and reactions $r = 1,\dots,R$ (reaction vectors $\zeta_r \in \mathbb{Z}^d$, intensities $\lambda_r$) is the continuous-time Markov chain

$$X(t) = X(0) + \sum_{r=1}^R Y_r\Big(\int_0^t \lambda_r(X(s))\,ds\Big)\zeta_r$$

with independent unit-rate Poisson processes $Y_r$ and initial law $\nu$; assume it is non-explosive and write $p_t^\nu(x) = P_\nu(X(t) = x)$ and $\lambda_0 = \sum_r \lambda_r$. Fix a split time $t - h$ with $h \in [0,t]$ and integers $n, m \ge 1$. Simulate $n$ independent paths $X_1,\dots,X_n$ on $[0, t-h]$; from each endpoint $X_i(t-h)$ simulate $m$ conditionally independent continuations $X_{i1},\dots,X_{im}$ on $[t-h, t]$. The **conditional Monte Carlo** (split-path) estimator is

$$\hat p_t^\nu(x; n, m, h) = \frac1n\sum_{i=1}^n \frac1m\sum_{j=1}^m \mathbb{1}\{X_{ij}(t) = x\},$$

which is unbiased; $m = 1$ (or $h = 0$) is the ordinary empirical estimator.

**Theorem (integrated mean squared error).** For all $n, m \ge 1$ and $h \in [0,t]$,

$$\mathbb{E}\Big[\sum_{x \in \mathbb{Z}_{\ge 0}^d}\big(\hat p_t^\nu(x;n,m,h) - p_t^\nu(x)\big)^2\Big] = \frac1n\Big[\frac1m + \Big(1 - \frac1m\Big)P_\nu\big(X_{11}(t) = X_{12}(t)\big) - \sum_x p_t^\nu(x)^2\Big],$$

where $X_{11}, X_{12}$ are two continuations sharing the path up to $t-h$.

**Theorem (cost).** The expected number of reaction events needed to produce one group $\{X_{1j}\}_{j=1}^m$ is

$$\mathbb{E}_\nu\Big[\int_0^{t-h}\lambda_0(X(s))\,ds\Big] + m\,\mathbb{E}_\nu\Big[\int_{t-h}^t \lambda_0(X(s))\,ds\Big].$$

**Theorem (coalescence probability).** Let $S = [\zeta_1 \cdots \zeta_R]$ be the $d \times R$ stoichiometric matrix and $\mathrm{null}(S) = \{k \in \mathbb{Z}^R : Sk = 0\}$ its integer right null space. Let $X$ be non-explosive and

$$Z(t) = X(0) + \sum_{r=1}^R Y_r^Z\Big(\int_0^t \lambda_r(X(s))\,ds\Big)\zeta_r,$$

with unit-rate Poisson processes $Y_r^Z$ independent of the $Y_r$ driving $X$, so that $Z$ uses the intensity path of $X$. Write $\Lambda_r^{0,t} = \int_0^t \lambda_r(X(s))\,ds$ and, given $\Lambda_r^{0,t}$, let $K_r^{0,t}$ have the Skellam$(\Lambda_r^{0,t}, \Lambda_r^{0,t})$ law, that of the difference of two independent Poisson variables with mean $\Lambda_r^{0,t}$. Then

$$P_\nu(X(t) = Z(t)) = \sum_{k \in \mathrm{null}(S)} \mathbb{E}_\nu\Big[\prod_{r=1}^R P\big(K_r^{0,t} = k_r \,\big|\, \Lambda_r^{0,t}\big)\Big],$$

where the expectation is over the random intensity integrals $\Lambda^{0,t} = (\Lambda_r^{0,t})_r$. Applied on $[t-h, t]$, under the approximation that the two continuations have nearly equal intensity integrals there (valid for small $h$), this yields a computable approximation of the collision term in the error formula.

## Proof sketch

Expanding the square and using that the $m$ continuations in a group are exchangeable and share their past, the variance per group is $\frac1m(1 - \sum p^2)$ from within-group noise plus $(1 - \frac1m)$ times the excess collision probability $P(X_{11}(t) = X_{12}(t)) - \sum_x p_t^\nu(x)^2$ caused by the shared prefix. Long $h$ makes continuations nearly independent (small collision term) but costs $m$ times more simulation on $[t-h,t]$; the two theorems therefore define an optimisation over $(m,h)$ at fixed computational budget, which the paper solves approximately and complements with a central limit theorem and a chi-square type confidence bound for the integrated squared error.

## Sources

- David F. Anderson and Kurt W. Ehlert, "Conditional Monte Carlo for Reaction Networks", *SIAM Journal on Scientific Computing* 44 (2022), A993–A1019, <https://doi.org/10.1137/21m144267x>. Preprint version: arXiv:1906.05353 (2019), estimator definition (Introduction), the mean integrated squared error theorem, the Skellam approximation theorem (Theorem 3.2) and the theorem on the expected number of reactions (Proofs section), <https://doi.org/10.48550/arXiv.1906.05353>.
