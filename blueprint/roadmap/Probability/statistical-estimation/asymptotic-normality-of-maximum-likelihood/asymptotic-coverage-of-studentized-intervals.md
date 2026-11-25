# Asymptotic coverage of studentized confidence intervals

Let $\theta \in \mathbb{R}$, $\sigma > 0$ and $r_n > 0$ with $r_n \to \infty$, and let estimators $\hat\theta_n$ and $\hat s_n > 0$ satisfy $r_n(\hat\theta_n - \theta) \to N(0, \sigma^2)$ in distribution and $\hat s_n \to \sigma$ in probability. Then $T_n = r_n(\hat\theta_n - \theta)/\hat s_n \to N(0, 1)$ in distribution, and for $0 < \alpha < 1$, with $z$ the $(1 - \alpha/2)$-quantile of $N(0, 1)$, the interval $[\hat\theta_n - z\hat s_n/r_n, \hat\theta_n + z\hat s_n/r_n]$ contains $\theta$ with probability tending to $1 - \alpha$.

Proof. The ratio form of Slutsky's theorem gives $T_n \to Z$ with $Z \sim N(0, 1)$. The interval contains $\theta$ exactly when $|T_n| \le z$, and the boundary $\{-z, z\}$ of $[-z, z]$ has $N(0, 1)$-probability zero, so $P(|T_n| \le z) \to P(|Z| \le z) = 1 - \alpha$.

## Proof depends on

- [Slutsky's theorem (ratio form)](div-of-tendsto-in-measure-const.md): studentization by the ratio form of Slutsky's theorem.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Convergence in distribution gives convergence of the probabilities of sets whose boundary is null for the limit law (portmanteau theorem).

## Sources

- J. Brunner, *Large-sample tools* (lecture slides, STA 442/2101), University of Toronto, Fall 2012, Slide 33, Slutsky theorems for convergence in distribution, <http://utstat.utoronto.ca/brunner/oldclass/appliedf12/lectures/2101f12LargeSample.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
