# The Gaussian mechanism

Let $f : X \to \mathbb{R}^d$ have $\ell_2$-sensitivity at most $\Delta_2 \ge 0$, i.e.
$\|f(x) - f(y)\|_2 \le \Delta_2$ for all neighbours. Let $\varepsilon \in (0, 1)$, $\delta > 0$, $c > 0$
with $c^2 > 2\ln(1.25/\delta)$, and $\sigma \ge c\Delta_2/\varepsilon$. Releasing $f(x) + Z$ with
$Z \sim N(0, \sigma^2 I_d)$ is $(\varepsilon, \delta)$-differentially private. Calibrating to the
$\ell_2$ rather than the $\ell_1$ sensitivity is what makes Gaussian noise attractive for
high-dimensional queries.

## Background

- [Laplace and exponential mechanisms](../laplace-and-exponential-mechanisms/README.md): the pure-privacy mechanisms; the Gaussian mechanism trades the $\delta$ for $\ell_2$ calibration.
- [Multivariate normal distribution](../../../Probability/distributions/continuous/multivariate-normal-distribution/README.md): the law of the noise, $N(0, \sigma^2 I_d)$.
- [Laplace distribution](../../../Probability/distributions/continuous/laplace-distribution/README.md): the noise law of the pure-privacy mechanism it is compared with.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Appendix A, Theorem A.1.
