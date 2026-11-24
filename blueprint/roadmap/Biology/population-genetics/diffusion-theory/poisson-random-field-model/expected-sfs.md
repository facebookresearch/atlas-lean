# Expected site frequency spectrum under the Poisson random field

For real numbers $\theta$ and $\sigma$ and natural numbers $n$ and $i$, let

$$\mathbb{E}\,\xi_i = \int_0^1 \binom{n}{i} x^i (1 - x)^{n - i}\, \varphi_{\theta,\sigma}(x)\, dx,$$

with the [Poisson random field density](prf-density.md) $\varphi_{\theta,\sigma}$, where the integral of a non-integrable function is taken to be $0$. For $\theta \ge 0$ and $1 \le i \le n$ it is the expected number of sites at which exactly $i$ of $n$ sampled gene copies carry the derived allele. The site frequency spectrum consists of the segregating classes $1 \le i < n$. The value at $i = n$ counts the sites at which every sampled copy is derived, which are monomorphic in the sample. For $i = 0$ the integrand behaves like $\theta/x$ near $0$, so it is not integrable when $\theta \ne 0$ (for $\theta > 0$, infinitely many ancestral-monomorphic sites are expected) and the value is $0$ by the convention; when $\theta = 0$ the integrand is identically $0$.

## Sources

- S. A. Sawyer and D. L. Hartl, *Population genetics of polymorphism and divergence*, Genetics 132 (1992), 1161–1176.
