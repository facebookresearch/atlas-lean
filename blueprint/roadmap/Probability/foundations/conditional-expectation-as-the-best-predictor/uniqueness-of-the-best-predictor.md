# Uniqueness of the best predictor

Let $\mu$ be a finite measure on $(\Omega, \mathcal{F})$, let $\mathcal{G} \subseteq \mathcal{F}$ be a sub-σ-algebra, and let $Y$ be square-integrable. If $g$ is $\mathcal{G}$-measurable and square-integrable and $\int (Y - g)^2\, d\mu \le \int (Y - h)^2\, d\mu$ for every square-integrable $\mathcal{G}$-measurable $h$, then $g = \mathbb{E}[Y \mid \mathcal{G}]$ almost everywhere. So the conditional expectation is the unique minimizer of the mean squared error up to almost-everywhere equality.

**Proof.** By the Pythagorean identity, $\int (Y - g)^2 = \int (Y - \mathbb{E}[Y \mid \mathcal{G}])^2 + \int (\mathbb{E}[Y \mid \mathcal{G}] - g)^2$. Taking $h = \mathbb{E}[Y \mid \mathcal{G}]$ in the hypothesis gives $\int (\mathbb{E}[Y \mid \mathcal{G}] - g)^2 \le 0$, so the nonnegative integrand vanishes almost everywhere.

## Proof depends on

- [Pythagorean identity for the conditional mean](integral-sq-sub-eq-integral-sq-sub-cond.md): the decomposition of the mean squared error of a $\mathcal{G}$-measurable predictor

## Background

- [The conditional mean minimizes the expected squared error](integral-sq-sub-cond-exp-le.md): existence of the minimizer, which this page shows is unique

## Sources

- B. D. O. Anderson and J. B. Moore, *Optimal Filtering*, Prentice-Hall, 1979, <https://users.cecs.anu.edu.au/~john/papers/BOOK/B02.PDF>, Section 2.3, Theorem 3.1 (pp. 26–27): a minimum variance estimate of $X$ given $Y = y$ is uniquely specified as the conditional mean, shown for jointly distributed vectors with a conditional density. The measure-theoretic statement up to almost-everywhere equality is derived on the page.
