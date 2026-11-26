# Step-size conditions for stability of fitness peaks under the breeder's equation

**System.** For a domain $D\subseteq\mathbb R^n$, $f\in C^1(D)$ with $\nabla f$ locally Lipschitz, and symmetric positive semidefinite matrices $P_k$,

$$x_{k+1}=x_k+P_k\nabla f(x_k),\qquad k=0,1,2,\dots$$

With $P_k=G_k$ (the additive genetic covariance matrix) and $f=\ln\bar W$ (log mean fitness) this is Lande's multivariate breeder's equation. Write $\lambda_1(P)\le\dots\le\lambda_n(P)$ for the eigenvalues.

**Hypotheses.** (H1) $f$ has an isolated local maximum at $\bar x$; (H2) $\bar x$ is an isolated critical point; (H3) $\sum_k\lambda_1(P_k)=\infty$. Let $r_0,L,\Lambda>0$ be such that $\overline B_{r_0}(\bar x)\subset D$, $\nabla f$ is $L$-Lipschitz on that ball and $\lambda_n(P_k)\le\Lambda$ for all $k$. Step conditions: (S1) $L\Lambda\le2$; (S2) $L\Lambda\le2-\eta$ for some $\eta\in(0,2]$.

**Theorem.**

- Under H1 and S1, $\bar x$ is uniformly stable.
- Under H1, H2, H3 and S2, $\bar x$ is uniformly asymptotically stable.
- Under H1, H2 and S1, uniform asymptotic stability also holds if $\sum_k\lambda_1(P_k)\big(2-L\lambda_n(P_k)\big)=\infty$, which allows $L\lambda_n(P_k)\to2$ slowly.
- Under further conditions on a sublevel set $\mathcal E$ of $f$, every sequence started in $\mathcal E$ exists for all time and converges to $\bar x$, so $\mathcal E$ lies in the basin of attraction.

**The step bound is necessary.** For $f(x)=-\frac a2x^2$ and $P_k\equiv p$, the iteration is $x_{k+1}=(1-pa)x_k$: it converges geometrically if $pa<2$, oscillates with constant amplitude if $pa=2$ (stable, not asymptotically stable), and diverges if $pa>2$, although $\bar x=0$ is an isolated maximum, $P_k$ is positive definite and $\sum_k\lambda_1(P_k)=\infty$. So the continuous-time result (stability whenever $P(t)$ is positive semidefinite) has no literal discrete analogue: too much additive genetic variance relative to the curvature of the log-fitness landscape makes the mean trait overshoot the peak.

## Depends on

- [Lande's selection gradient](../lande-s-selection-gradient/README.md)
- [Breeder's equation](../breeder-s-equation/README.md)

## Expansion

The key estimate is a descent inequality: for $L$-Lipschitz $\nabla f$, $f(x_{k+1})\ge f(x_k)+\nabla f^\top P_k\nabla f-\frac L2|P_k\nabla f|^2\ge f(x_k)+\big(1-\frac L2\lambda_n(P_k)\big)\nabla f^\top P_k\nabla f$, so $f$ is nondecreasing along iterates when $L\lambda_n\le2$, and a sublevel set around the isolated maximum traps the orbit. With a margin $\eta$ the increase is at least $\frac\eta2\lambda_1(P_k)|\nabla f|^2$, and divergence of $\sum\lambda_1(P_k)$ forces $\nabla f(x_k)\to0$, hence convergence to the isolated critical point.

## Sources

- B. J. Ridenhour, "Stability of equilibria in discrete-time modified-gradient systems and the multivariate breeder's equation", arXiv:2611.14756 (2026), Section 2 (hypotheses H0–H3, S1–S2), Section 3 (Example of failure), Theorem 5.1, Corollary 5.2, Theorem 6.1, <https://doi.org/10.48550/arXiv.2611.14756>.
