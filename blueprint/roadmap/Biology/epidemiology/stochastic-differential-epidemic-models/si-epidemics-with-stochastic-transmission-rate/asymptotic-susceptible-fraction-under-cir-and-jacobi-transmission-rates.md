# Asymptotic susceptible fraction under CIR and Jacobi transmission rates

**Model.** In a closed population let $S_t \in [0,1]$ be the susceptible fraction of an SI epidemic with random transmission rate $\beta_t = \varphi(t)P_t$:

$$\frac{dS_t}{dt} = -\beta_t S_t(1 - S_t), \qquad S_0 = s_0 \in (0,1),$$

where $\varphi > 0$ is a deterministic intervention profile and $(P_t)_{t\ge0}$ a positive stochastic process describing the uncontrolled infection rate. Let $H_t = \int_0^t \beta_s\,ds$ be the **integrated transmission intensity**.

**Proposition (pathwise solution).** If $\beta$ has a.s. continuous paths, the equation has the unique global solution

$$S_t = \Big[1 + \Big(\frac{1}{s_0} - 1\Big)e^{H_t}\Big]^{-1},$$

so $S_\infty = [1 + (1/s_0 - 1)e^{H_\infty}]^{-1}$ is determined by $H_\infty \in (0,\infty]$.

**Theorem (successful intervention).** If $\int_0^\infty \varphi(s)\,ds < \infty$ and $P$ has a.s. continuous positive paths with $\sup_t \mathbb E[P_t] < \infty$, then $H_\infty < \infty$ a.s. and $S_\infty \in (0, s_0)$ a.s.: a positive fraction escapes infection.

**Theorem (no intervention).** If $\varphi \equiv 1$ and $P$ is an ergodic Markov process with a unique stationary law $\pi$ on $(0,\infty)$ of finite positive mean, then $H_\infty = \infty$ a.s. and $S_\infty = 0$ a.s.

**CIR intensity.** For the Cox–Ingersoll–Ross process $dP_t = \kappa(\eta - P_t)dt + \sigma\sqrt{P_t}\,dW_t$, $\mathbb E[H_t] = \int_0^t [\eta + (p_0 - \eta)e^{-\kappa s}]\,ds$, and for $0 < \lambda < \lambda_c = \kappa^2/(2\sigma^2)$

$$\mathbb E[e^{\lambda H_t}\mid P_0 = p_0] = \exp\{A(t,\lambda) + B(t,\lambda)p_0\},$$

with $A, B$ explicit solutions of Riccati equations (written with $\gamma = \sqrt{\kappa^2 - 2\sigma^2\lambda}$). Hence, for the time $\tau$ at which $H$ first reaches a threshold $M$ (equivalently, the infected fraction reaches a prescribed level),

$$\mathbb P(\tau \le t) \le \inf_{0<\lambda<\lambda_c}\exp\{-\lambda M + A(t,\lambda) + B(t,\lambda)p_0\}.$$

Write $\Lambda_t(\lambda) = A(t,\lambda) + B(t,\lambda)p_0$ and $\Lambda_t'(\lambda_c-) = \lim_{\lambda\uparrow\lambda_c}\partial_\lambda\Lambda_t(\lambda)$, which is finite for fixed $t$. The exponent $-\lambda M + \Lambda_t(\lambda)$ is strictly convex in $\lambda$, and if $\mathbb E_{p_0}[H_t] < M < \Lambda_t'(\lambda_c-)$ it has a unique minimizer $\lambda^*(M) \in (0,\lambda_c)$, the solution of $\partial_\lambda\Lambda_t(\lambda) = M$, which increases strictly in $M$ on that interval. For $M \ge \Lambda_t'(\lambda_c-)$ the infimum over $(0,\lambda_c)$ is approached as $\lambda \uparrow \lambda_c$ and is not attained.

## Proof sketch

The SI equation is logistic in the random clock $H_t$, so all long-run questions reduce to whether $H_\infty$ is finite. An integrable intervention with bounded-mean $P$ gives $\mathbb E[H_\infty] < \infty$; without intervention the ergodic theorem gives $H_t/t \to \int x\,\pi(dx) > 0$. The CIR process is affine, so the Laplace transform of its time integral solves Riccati equations, which turns the threshold-crossing probability into a Chernoff bound. Since $\partial_\lambda\Lambda_t(0) = \mathbb E_{p_0}[H_t]$ and $\partial_\lambda\Lambda_t$ is strictly increasing, the first-order condition $\partial_\lambda\Lambda_t(\lambda)=M$ has a root in $(0,\lambda_c)$ exactly for $M$ between these two derivatives. The Jacobi process (bounded on an interval) has the same mean formula with its own long-run mean.

## Sources

- León A. Valencia, Raúl Alejandro Morán-Vásquez and Duván H. Cataño Salazar, "Modeling transmission intensity in SI epidemics via CIR and Jacobi processes: Asymptotic results and preliminary intervention strategies", *Mathematical Biosciences and Engineering* 23 (2026), 1995–2017, <https://doi.org/10.3934/mbe.2026073>. Preprint version: arXiv:2604.02224 (2026), Proposition 2.1, Theorems 2.2–2.3, Lemmas 2.4–2.5, Propositions 2.6–2.7, Corollary 2.8, Proposition 2.9, <https://doi.org/10.48550/arXiv.2604.02224>.
