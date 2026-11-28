# Consistent estimation of engineering resilience from a single trajectory

**Setting.** A $d$-species birth-and-death process $N^K$ with rates $K B_j(n/K)$, $K D_j(n/K)$, deterministic limit $\dot x = B(x) - D(x)$ with globally attracting interior fixed point $x^*$, Jacobian $M^*$, quasi-stationary distribution $\nu_K$ and engineering resilience $\rho^* = -\sup \operatorname{Re}\operatorname{Sp}(M^*)$, under the standing hypotheses of [covariance relations for the quasi-stationary distribution](covariance-relations-for-the-quasi-stationary-distribution-of-birth-and-death-processes.md). From one observed path $(N^K(s))_{0 \le s \le T}$ define the time averages

$$S^\mu_p(T,K) = \frac1T\int_0^T N^K_p(s)\,ds,$$

$$S^C_{pq}(T,\tau,K) = \frac{1}{T-\tau}\int_0^{T-\tau} \bigl(N^K_p(s+\tau) - S^\mu_p\bigr)\bigl(N^K_q(s) - S^\mu_q\bigr)\,ds,$$

the empirical matrix $M^*_{\mathrm{emp}}$ by $e^{\tau M^*_{\mathrm{emp}}(T,\tau,K)} = S^C(T,\tau,K)\, S^C(T,0,K)^{-1}$, and the empirical resilience $\rho^*_{\mathrm{emp}}(T,\tau,K) = -\sup\{\operatorname{Re} z : z \in \operatorname{Sp}(M^*_{\mathrm{emp}})\}$.

**Theorem 3.4 (time averages before extinction).** Time averages $S_f(T,K) = \frac1T\int_0^T f(N^K(s))\,ds$ of polynomially bounded observables approximate the quasi-stationary expectations $\nu_K(f)$ as long as $T$ is far below the extinction time scale. For the mean, the source summarizes the bound in the form: for every initial state $n$,

$$\bigl|\mathbb E_n[S^\mu_p(T,K)] - \mu^K_p\bigr| \le C\,(K + \|n\|_1)\Bigl(\frac{1 + \log K}{T} + e^{-c(\|n\|_1 \wedge K)} + T e^{-c'K}\Bigr),$$

with positive constants $c, c', C$; the precise statement of Theorem 3.4 has, in addition, an exponentially small term in the killing rate of $\nu_K$. With $n = \Theta(K)$ and $T = \Theta(K^{a+1}\log K)$ the bias is $O(K^{-a})$, while for $T$ of order $e^{\Theta(K)}$ or larger the average collapses to $0$ because the process has been absorbed.

**Theorem 5.7 (consistency of the empirical resilience).** For a lag $\tau = \Theta(1)$, an initial state $n = \Theta(K)$, $0 < T \ll \exp(\Theta(K))$ and $K$ large enough, with probability at least $1 - 1/K$,

$$\bigl|\rho^*_{\mathrm{emp}}(T,\tau,K) - \rho^*\bigr| \le C\Bigl(\frac{K^2}{\sqrt T} + \frac{1}{\sqrt K}\Bigr).$$

In particular, if $T \ge K^5$ then $|\rho^*_{\mathrm{emp}} - \rho^*| \le C/\sqrt K$.

For one species the fluctuation-dissipation relation gives a second estimator, $\rho^* \approx S^{\mathcal D}/S^\Sigma$, where $S^{\mathcal D}(T,K)$ is the number of births up to time $T$ divided by $T$ (an estimator of $K B(x^*)$) and $S^\Sigma(T,K)$ is the empirical variance; its error is controlled in the same regimes.

## Expansion

The proof combines three ingredients. Exponential mixing towards the quasi-stationary law on time scales of order $\log K$ for initial states of order $K$, together with the exponentially small killing rate, makes time averages behave like ergodic averages for the conditioned process (Proposition 3.3 and Theorem 3.4). Variance bounds for the estimators (Propositions 5.1 and 5.3-5.6, Corollary 5.2) show that $S^C(T,0,K)$ and $S^C(T,\tau,K)$ are within $O(K^2/\sqrt T)$ relative accuracy of $\Sigma^K(0)$ and $\Sigma^K(\tau)$, with Chebyshev's inequality giving the probability $1 - 1/K$. Finally, the regression relation $\Sigma^K(\tau) = e^{\tau M^*}\Sigma^K(0) + O(\sqrt K)$ with $\Sigma^K(0) \ge cK\,\mathrm{Id}$ turns these into an $O(K^{-1/2})$ approximation of $e^{\tau M^*}$, and continuity of the spectrum transfers the error to the spectral abscissa. The lag must be of order one: for $\tau \to 0$ the matrix $e^{\tau M^*}$ is too close to the identity, and for $\tau$ of order $\log K$ the signal $e^{\tau M^*}\Sigma^K(0)$ drops to the size of the error term.

## Depends on

- [Covariance relations for the quasi-stationary distribution of birth-and-death processes](covariance-relations-for-the-quasi-stationary-distribution-of-birth-and-death-processes.md)

## Sources

- J.-R. Chazottes, P. Collet, S. Martínez, S. Méléard, "Quasi-stationary distributions and resilience: what to get from a sample?" (2019), Section 1.2 (estimators and the main theorem), Section 3 (Proposition 3.3, Theorem 3.4), Section 5 (Propositions 5.1 and 5.3-5.6, Corollary 5.2, Theorem 5.7) and Appendix B, <https://doi.org/10.48550/arXiv.1906.05635>.
