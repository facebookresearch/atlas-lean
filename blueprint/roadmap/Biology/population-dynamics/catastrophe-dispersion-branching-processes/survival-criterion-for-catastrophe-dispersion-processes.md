# Survival criterion for catastrophe–dispersion processes in varying and random environments

**Model.** Each colony starts from one individual and grows internally as $\eta(t)$ until a catastrophe at an independent time $T$; given $\eta(T) = m$, a random number $N_m \in \{0, \dots, m\}$ survive (stochastically nondecreasing in $m$; e.g. binomial with survival probability $p$). The $r$ survivors found $\Delta(r)$ new colonies, where the dispersal operator is one of
- (D1) full dispersal $\Delta^{(1)}(r) = r$;
- (D2) capacity-limited $\Delta^{(2)}(r) = \min\{d, r\}$;
- (D3) independent site occupation: survivors pick one of $d$ sites uniformly and independently, $\Delta^{(3)}(r)$ = number of occupied sites;
- (D4) uniform dispersal: all occupancy vectors of $r$ survivors on $d$ territories equally likely, $\Delta^{(4)}(r)$ = number of occupied territories.

Generation $n$ uses environment $\mathcal E_n$ (growth, catastrophe and dispersal parameters). Let $\mu_n = \mathbb E[\Delta(N_{\eta(T)}) \mid \mathcal E_n]$, $\ell_n = \log \mu_n$, $S_n = \sum_{k<n} \ell_k$, and $Z_n$ the number of colonies.

**Theorem.**
1. *(Ordering.)* For every environment and every law of survivors, $\mu^{(4)} \le \mu^{(3)} \le \mu^{(2)} \le \mu^{(1)}$.
2. *(Varying environment.)* If $0 < \mu_n < \infty$ and $\overline\Lambda = \limsup S_n/n < 0$ then $Z_n \to 0$ a.s.; if $\underline\Lambda = \liminf S_n/n > 0$ then $\mathbb P(Z_n \to \infty) > 0$.
3. *(Random environment.)* For a stationary ergodic environment with $\mathbb E|\ell_0| < \infty$ and $\mathbb E\bigl|\log \mathbb P(\xi_{1,0} > 0 \mid \mathcal E_0)\bigr| < \infty$, let $\Lambda = \mathbb E[\ell_0]$. Survival has positive probability if $\Lambda > 0$; extinction is a.s. if $\Lambda < 0$, and also if $\Lambda = 0$ with non-degenerate offspring law.
4. *(Poisson growth, binomial catastrophe.)* Let $\eta(t) = 1 + X(t)$ with $X$ Poisson of rate $\lambda$, $T \sim \mathrm{Exp}(\theta)$ and binomial survival with probability $p$. If $(\theta_n, \lambda_n, p_n) \to (\theta, \lambda, p)$ with $\theta > \lambda$ and $d_n \to \infty$, then for all four mechanisms the process is supercritical if $p > \theta/(\theta + \lambda)$ and dies out a.s. if $p < \theta/(\theta + \lambda)$.

## Expansion

Conditionally on the environment, colonies reproduce independently with the induced offspring law, so the process is a Galton–Watson process in a varying or random environment and the classical log-mean criteria (Jagers; Smith–Wilkinson; Kersting–Vatutin) apply to $\mu_n$ even though the offspring law is only given implicitly. The ordering follows from $\Delta^{(3)}(Y) \le \min(d, Y) \le Y$ pathwise and a comparison of occupancy distributions for (D4). In the Poisson–binomial example the mean number of survivors is $p\,(1 + \lambda/\theta)$, and as $d \to \infty$ every capacity-limited mechanism behaves like full dispersal, giving the common threshold $p(\theta+\lambda)/\theta = 1$.

## Sources

- L. R. de Lima, F. P. Machado, "Catastrophe-dispersion models in random and varying environments across generations", arXiv:2605.04048 (2026), Lemma on ordering of induced offspring means (Section 4), Theorems 4.1, 4.2 and 4.3, <https://doi.org/10.48550/arXiv.2605.04048>.
