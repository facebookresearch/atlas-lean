# Stability of fitness maxima under modified-gradient dynamics with a time-varying G-matrix

The continuous-time multivariate breeder's (Lande) equation $\dot{\bar{\mathbf z}} = \mathbf{G}(t) \nabla \ln \bar W(\bar{\mathbf z})$ is a **modified-gradient system**

$$ \mathbf{x}' = P(t)\, \nabla f(x), \qquad \text{(E)} $$

with $P(t) = \mathbf{G}(t)$ the genetic variance-covariance matrix and $f = \ln \bar W$ the log mean fitness.

**Hypotheses.** (H0) $D \subset \mathbb{R}^n$ is a domain, $f \in C^1(D)$ with $C^1$ gradient, and $P(t)$, $t \ge 0$, is an $n \times n$ matrix with $C^1$ entries that is positive semi-definite. (H1) $f$ has an isolated local maximum at $\bar x \in D$. (H2) $\bar x$ is an isolated critical point of $f$. (H3) the eigenvalue condition

$$ \int_0^\infty \lambda_1(P(t))\, dt = \infty $$

holds, where $\lambda_1(P(t))$ is the smallest eigenvalue of $P(t)$.

**Theorem 1.** Under (H0) and (H1), $\bar x$ is a uniformly stable equilibrium of (E). Under (H0)-(H3), $\bar x$ is uniformly asymptotically stable.

**Theorem 2 (basin of attraction).** Assume (H0)-(H3), let $M = f(\bar x)$, $c < M$, and let $E_{c,\bar x}$ be the connected component containing $\bar x$ of the open set $\{\bar x\} \cup \{ x : c < f(x) < M \}$. If (H4) $E_{c,\bar x}$ is bounded with closure in $D$, (H5) $f = c$ on $\partial E_{c,\bar x}$, and (H6) $f$ has no critical point in $\overline{E_{c,\bar x}}$ other than $\bar x$, then every solution of (E) starting in $E_{c,\bar x}$ converges to $\bar x$.

So a fitness peak is reached even when the G-matrix changes over time or is singular at times (genetic constraints in some directions), provided the smallest genetic variance is not integrable: the population cannot be permanently starved of variation in any direction.

## Depends on

- [Lande's gradient form of the response, genetic-covariance version](../lande-s-selection-gradient/selected-shift-breeding-eq-gradient-gene.md)

## Proof depends on

- [Lyapunov's direct method and Lyapunov's instability theorem](../../../Analysis/ordinary-differential-equations/lyapunov-s-direct-method/lyapunov-s-direct-method-and-lyapunov-s-instability-theorem.md)

## Expansion

The function $V(x) = f(\bar x) - f(x)$ is positive near $\bar x$ (by H1) and nonincreasing along solutions, since $V'(t) = -\nabla f^\top P(t) \nabla f \le 0$ by positive semi-definiteness; this gives uniform stability. Moreover $V' \le -\lambda_1(P(t)) |\nabla f(x(t))|^2$. If a solution stayed in an annulus around $\bar x$, where $|\nabla f|$ is bounded below by (H2), integrating and using (H3) would force $V \to -\infty$, a contradiction; uniformity in the starting time follows because the estimate depends only on the integral of $\lambda_1$. For the basin, the sublevel structure of $f$ makes $E_{c,\bar x}$ positively invariant (solutions cannot cross the level set $f = c$ while $f$ is nondecreasing along them), and the same integral argument rules out accumulation away from $\bar x$ when no other critical points exist there.

## Sources

- Benjamin J. Ridenhour and Jerry R. Ridenhour, *Stability of equilibria in quantitative genetic models based on modified-gradient systems*, J. Biol. Dyn. 12(1) (2018), 39–50. <https://doi.org/10.1080/17513758.2017.1400598> Section 2 (hypotheses H0–H3, Theorem 1) and Section 3 (Theorem 2). Locators use the numbering of the preprint, titled *Stability of equilibria in modified-gradient systems*, arXiv:1608.04423.
