# Symmetric Bernoulli law

The symmetric Bernoulli law is the probability measure $\frac12 \delta_{-1} + \frac12 \delta_1$ on
$\mathbb{R}$, where $\delta_a$ is the Dirac mass at $a$: it puts mass $1/2$ at each of the points $-1$
and $1$.

## Idea

This is the law of a fair coin flip with values $\pm 1$, the step of the simple random walk. Integrals
against it are averages, $\int f \, d\mu = \frac12 f(-1) + \frac12 f(1)$, so all its moments are finite
and easy to compute: mean $0$, variance $1$ and third absolute moment $1$, the smallest value possible
for a standardized law. Being concentrated on two points, it shows that the class of standardized
two-point laws is not empty. It also shows that the rate $1/\sqrt{n}$ in the Berry–Esseen theorem
cannot be improved: for even $n$ the sum of $n$ independent copies is $0$ with probability
$\binom{n}{n/2} 2^{-n} \approx \sqrt{2/(\pi n)}$, so the distribution function of the normalized sum
jumps by that amount at $0$, where $\Phi$ is continuous.

## Statements

- [Symmetric Bernoulli law](symmetric-bernoulli-law.md)
- [The symmetric Bernoulli law has moments of all orders](symmetric-bernoulli-mem-lp.md): basic property: moments of all orders
- [Integrals against the symmetric Bernoulli law](symmetric-bernoulli-integral.md): formula for integrals against the law
- [Third absolute moment of the symmetric Bernoulli law](symmetric-bernoulli-third-moment.md): computation of the third absolute moment
- [The symmetric Bernoulli law is standardized](symmetric-bernoulli-is-standardized.md): example of a standardized law
- [The symmetric Bernoulli law is a standardized two-point law](symmetric-bernoulli-is-bernoulli.md): example of a standardized two-point law
