# Gamma–Poisson conjugacy

Let $a, b > 0$ and $k \in \mathbb{N}$, and let $g_{a,b}(r) = \frac{b^a}{\Gamma(a)} r^{a-1} e^{-br}$ for
$r \ge 0$ and $g_{a,b}(r) = 0$ for $r < 0$ be the gamma density with shape $a$ and rate $b$, where at
$r = 0$ the real power $r^{a-1}$ is $0$ when $a \ne 1$ and $1$ when $a = 1$. For every real $r$,

$$\frac{e^{-r} r^k / k! \cdot g_{a, b}(r)}{p_{\Gamma(a, b)}(k)} = g_{a + k, b + 1}(r),$$

where $p_{\Gamma(a, b)}(k) = \mathrm{NB}(k; a, a/b)$ is the mass at $k$ of the mixed Poisson law over
$\Gamma(a, b)$: with prior $\Lambda \sim \Gamma(a, b)$ and one observation $N = k$ from
$\operatorname{Poisson}(\Lambda)$, the posterior law of $\Lambda$ is $\Gamma(a + k, b + 1)$.

## Idea

Bayes' rule multiplies the prior density by the likelihood and divides by the marginal mass. For a
gamma prior and a Poisson count, the product $e^{-r} r^k \cdot r^{a-1} e^{-br}$ is again a gamma kernel,
with shape $a + k$ and rate $b + 1$, so the posterior stays in the gamma family: the gamma laws are
conjugate priors for the Poisson likelihood. The marginal mass is the negative binomial mass of the
Greenwood–Yule mixture. A further count $N'$, Poisson with the same rate $\Lambda$ and conditionally
independent of $N$ given $\Lambda$, is then, given $N = k$, a Poisson mixture over the posterior, so it
has the negative binomial law with size $a + k$ and mean $(a + k)/(b + 1)$. The conditional independence
is needed: $N' = N$ is also Poisson with rate $\Lambda$ given $\Lambda$, but given $N = k$ it is the point
mass at $k$.

## Statements

- [Gamma–Poisson conjugacy, posterior](gamma-pdfreal-posterior.md)
- [Gamma–Poisson conjugacy, posterior predictive](posterior-predictive-gamma-poisson.md): the posterior predictive law: given $N = k$, a further Poisson count with the same rate $\Lambda$, conditionally independent of $N$ given $\Lambda$, has the negative binomial law with size $a + k$ and mean $(a + k)/(b + 1)$

## Background

- [Mixed Poisson distributions](../mixed-poisson/README.md): the mixed Poisson mass
- [Negative binomial distribution](../negative-binomial/README.md): the negative binomial mass
- [Gamma–Poisson mixture (Greenwood–Yule)](../gamma-poisson-mixture/README.md): the marginal mass is a negative binomial mass
