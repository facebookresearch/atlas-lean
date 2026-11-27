# Almost-sure site frequency spectrum of an exponentially growing branching population

**Model.** Let $(Z(t))_{t\ge0}$ be a continuous-time Galton–Watson process with $Z(0) = 1$: each individual lives an $\mathrm{Exp}(a)$ time and then produces $k$ offspring with probability $u_k$, where $m = \sum_k k u_k > 1$ (supercritical) and $\sum_k k^3 u_k < \infty$. The net growth rate is $\lambda = a(m-1)$, $p$ is the extinction probability, $q = 1-p$, and $\Omega_\infty$ is the event of survival. Each individual accumulates neutral mutations at rate $\nu > 0$ under the infinite-sites model. The site frequency spectrum $S_j(t)$ is the number of mutations carried by exactly $j$ individuals alive at time $t$; $M(t)$ is the total number of mutations present; $\tau_N = \inf\{t : Z(t) \ge N\}$; $p_j(s) = \mathbb{P}(Z(s) = j \mid Z(0) = 1)$; and $Y = \lim_t e^{-\lambda t}Z(t)$.

**Theorem.** Conditionally on $\Omega_\infty$, almost surely, for every $j \ge 1$:

1. *(Fixed time)* $\displaystyle \lim_{t\to\infty} e^{-\lambda t} S_j(t) = \nu\, Y \int_0^\infty e^{-\lambda s} p_j(s)\, ds$;
2. *(Fixed size)* $\displaystyle \lim_{N\to\infty} N^{-1} S_j(\tau_N) = \nu \int_0^\infty e^{-\lambda s} p_j(s)\, ds$;
3. the same holds for $M$ with $p_j(s)$ replaced by $1 - p_0(s)$.

**Birth–death case.** If $u_0 + u_2 = 1$ with $u_2 > u_0$, then $p = u_0/u_2$, $Y \mid \Omega_\infty \sim \mathrm{Exp}$ with mean $1/q$, and

$$\lim_{N\to\infty} N^{-1}S_j(\tau_N) = \frac{\nu q}{\lambda}\int_0^1 \frac{(1-y)\,y^{j-1}}{1-py}\,dy = \frac{\nu q}{\lambda}\sum_{k=0}^\infty \frac{p^k}{(j+k)(j+k+1)}, \qquad \lim_{N\to\infty} N^{-1}M(\tau_N) = -\frac{\nu q \log q}{\lambda p}\ (0 < p < 1),$$

with the fixed-time versions obtained by multiplying by $Y$. For the pure-birth (Yule) process ($p = 0$) the limit is $\frac{\nu}{\lambda}\cdot\frac{1}{j(j+1)}$, and $M(\tau_N)/N \to \nu/\lambda$.

**Estimators.** In the birth–death case the long-run proportion of mutations carried by exactly one individual is the same at fixed time and fixed size and equals

$$\varphi_1(p) = \frac12 \ (p = 0), \qquad \varphi_1(p) = -\frac{p + q\log q}{p\log q} \ (0 < p < 1),$$

a strictly decreasing function with values in $(0, 1/2]$. Hence $\hat p = \varphi_1^{-1}(\text{observed singleton proportion})$ is a strongly consistent estimator of the extinction probability, and the total mutation count per individual, $M(\tau_N)/N$, then yields a consistent estimator of the effective mutation rate $\nu/\lambda$.

## Expansion

A mutation arising at time $s$ in one individual is carried, at time $t$, by that individual's clone, which has $j$ members with probability $\approx p_{j}(t-s)$; mutations arise at rate $\nu Z(s) \approx \nu Y e^{\lambda s}$. Summing over arrival times gives $\nu Y e^{\lambda t}\int_0^\infty e^{-\lambda u} p_j(u)\,du$. The almost-sure statement needs a second-moment bound on the fluctuations of the clone counts (finite third moment of the offspring law) plus Borel–Cantelli along a lattice of times; the fixed-size result follows because $\tau_N - \lambda^{-1}\log(N/Y) \to 0$ almost surely, cancelling $Y$. The $1/(j(j+1))$ law is the classical Luria–Delbrück/Durrett spectrum of a growing population, here obtained as an almost-sure limit rather than in expectation.

## Sources

- Einar Bjarki Gunnarsson, Kevin Leder and Xuanming Zhang, "Limit theorems for the site frequency spectrum of neutral mutations in an exponentially growing population", Stochastic Processes and their Applications 182 (2025), 104565, <https://doi.org/10.1016/j.spa.2025.104565>; numbering as in arXiv:2307.03346: Section 2, Theorem 1, Propositions 1–2, Corollary 1 and Section 5.
