# Integral of the folded count from unfolded integrals $\theta/j$

Let $\mu$ be a measure on a measurable space $\Omega$, $\theta$ a real number, $n$ and $i$ natural
numbers with $i \ge 1$ and $2i \le n$, and $\xi_j$ ($j \in \mathbb{N}$) $\mu$-integrable real
functions on $\Omega$ with

$$\int \xi_j \, d\mu = \frac{\theta}{j} \quad \text{for every } 1 \le j \le n - 1.$$

Then the [folded count](folded-count.md) $\eta_i$ satisfies

$$\int \eta_i \, d\mu
= \frac{\theta \left(\frac{1}{i} + \frac{1}{n-i}\right)}{1 + \delta_{i,n-i}},$$

where $\delta_{i,n-i}$ is $1$ if $i = n - i$ and $0$ otherwise: the integral is
$\theta/i + \theta/(n-i)$ when $2i < n$ and $\theta/i$ when $2i = n$. No normalisation of $\mu$ is
needed; when $\mu$ is a probability measure and the $\xi_j$ have Fu's
[expected site frequency spectrum](integral-sfs.md) $\theta/j$, this is the expected folded
spectrum.
