# Covariance relations for the quasi-stationary distribution of birth-and-death processes

**Setting.** A $d$-species population $N^K(t) \in \mathbb{Z}_{\ge 0}^d$ jumps by $+e_j$ at rate $K B_j(n/K)$ and by $-e_j$ at rate $K D_j(n/K)$ from state $n$. The rescaled process follows, over finite time horizons as $K \to \infty$, the ODE $\dot x = X(x) := B(x) - D(x)$. Assume (hypotheses H.1-H.8 of the source) that $B$ and $D$ are smooth with polynomially bounded second derivatives and vanish only at $0$, that $X$ has a unique globally attracting interior fixed point $x^*$ with $0$ repelling and $X$ pointing inward on the boundary, that the deterministic flow comes down from infinity in finite time, and that $\inf_j \partial_{x_j} B_j(0) > 0$ and $D_j(x) \ge \xi \max_\ell x_\ell$. Then $0$ is absorbing, extinction occurs at a time of order $e^{\Theta(K)}$, and there is a unique quasi-stationary distribution $\nu_K$ (the law of the process conditioned on non-extinction). Let

$$M^* = DX(x^*), \qquad \mu^K = \int n\, d\nu_K(n), \qquad \Sigma^K_{pq}(\tau) = \mathbb{E}_{\nu_K}\bigl[(N^K_p(\tau) - \mu^K_p)(N^K_q(0) - \mu^K_q)\bigr],$$

and $\Sigma^K = \Sigma^K(0)$. All spectral values of $M^*$ have negative real part, and the **engineering resilience** is $\rho^* = -\sup\{\operatorname{Re} z : z \in \operatorname{Sp}(M^*)\} > 0$.

**Theorem 1.1 (Onsager-type regression relation).** For every $\tau \ge 0$,

$$\Sigma^K(\tau) = e^{\tau M^*} \Sigma^K(0) + O(\sqrt K).$$

Since $\Sigma^K(0)$ is invertible and of order $K$ (Proposition 2.9, Corollary 2.8), this gives $e^{\tau M^*} = \Sigma^K(\tau)\Sigma^K(0)^{-1} + O(K^{-1/2})$ for fixed $\tau$.

**Theorem 1.2 (fluctuation-dissipation relation).** With $\mathcal D^K$ the diagonal matrix $\mathcal D^K_{pp} = K B_p(x^*) = K D_p(x^*)$,

$$M^* \Sigma^K + \Sigma^K (M^*)^{\mathsf T} + 2\mathcal D^K = O(\sqrt K).$$

For one species ($d = 1$) this determines the resilience:

$$\rho^* = \frac{K\bigl(B(x^*) + D(x^*)\bigr)}{2\Sigma^K} + O(K^{-1/2}).$$

**Theorem C.1 (Gaussian limit).** The image of $\nu_K$ under $n \mapsto (n - \lfloor K x^* \rfloor)/\sqrt K$ converges weakly to a centered Gaussian measure, whose covariance $\mathcal S = \lim_{K\to\infty} \Sigma^K/K$ is the unique symmetric solution of a Lyapunov equation. Dividing Theorem 1.2 by $K$ gives this equation as $M^*\mathcal S + \mathcal S (M^*)^{\mathsf T} + 2\operatorname{diag}(B(x^*)) = 0$, i.e. $\mathcal S = \int_0^\infty e^{\tau M^*}\, 2\operatorname{diag}(B(x^*))\, e^{\tau (M^*)^{\mathsf T}}\, d\tau$; the noise term is the total jump rate $B + D = 2B$ at $x^*$. (The display in the statement of Theorem C.1 in the source writes the noise term as $\operatorname{diag}(B(x^*))$; the normalization given here is the one consistent with Theorem 1.2 and with the remark following Theorem C.1.)

## Expansion

Both relations come from Dynkin's formula applied under the quasi-stationary law. For the regression relation, the mean drift of $N^K$ near $K x^*$ is $K X(N^K/K) \approx M^*(N^K - K x^*)$; moment bounds for $\nu_K$ (Theorem 2.6: centered moments of order $2q$ are $O(K^q)$, Proposition 2.7: $\mu^K - Kx^* = O(1)$) make the quadratic Taylor remainder $O(1)$ per unit of order-$\sqrt K$ fluctuation, so $\frac{d}{d\tau}\Sigma^K(\tau) = M^*\Sigma^K(\tau) + O(\sqrt K)$ and Gronwall gives the matrix exponential. For the fluctuation-dissipation relation, apply the generator to $n_p n_q$: the drift contributes $M^*\Sigma + \Sigma (M^*)^{\mathsf T}$ and the jump noise contributes $\operatorname{diag}(K(B_p + D_p))$ evaluated near $x^*$, equal to $2\mathcal D^K$ to leading order, and stationarity of $\nu_K$ up to the exponentially small killing rate makes the sum vanish to the stated order. For $d \ge 2$ the Lyapunov equation does not determine a non-symmetric $M^*$ from $\Sigma^K$ and $\mathcal D^K$, which is why the lagged covariances of Theorem 1.1 are needed.

## Sources

- J.-R. Chazottes, P. Collet, S. Martínez, S. Méléard, "Quasi-stationary distributions and resilience: what to get from a sample?" (2019), Section 1.2 (Theorem 1.1), Section 1.3 (Theorem 1.2), Section 2 (Theorem 2.6, Proposition 2.7, Corollary 2.8, Proposition 2.9), Section 4 (proofs) and Appendix C (Theorem C.1), <https://doi.org/10.48550/arXiv.1906.05635>.
