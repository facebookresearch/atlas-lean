# Gamma–Poisson conjugacy, posterior

Let $a, b > 0$, $k \in \mathbb{N}$, and let $g_{a, b}$ be the gamma density with shape $a$ and rate $b$
($g_{a, b}(r) = \frac{b^a}{\Gamma(a)} r^{a-1} e^{-br}$ for $r \ge 0$, $0$ for $r < 0$, where at $r = 0$ the
real power $r^{a-1}$ is $0$ when $a \ne 1$ and $1$ when $a = 1$). For every real $r$,

$$\frac{e^{-r} r^k / k! \cdot g_{a, b}(r)}{p_{\Gamma(a, b)}(k)} = g_{a + k, b + 1}(r),$$

where $p_{\Gamma(a, b)}(k) = \mathrm{NB}(k; a, a/b)$ is the [mixed Poisson mass](../mixed-poisson/poisson-mixture-real.md)
over the gamma law: with prior $\Lambda \sim \Gamma(a, b)$ and one observation $N = k$ from
$\operatorname{Poisson}(\Lambda)$, the posterior is $\Gamma(a + k, b + 1)$.
