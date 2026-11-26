# Limit laws for linear functionals of the Pitman–Yor frequency spectrum

**Setting.** For $0 < \alpha < 1$ and $\theta > -\alpha$ the **Pitman–Yor sampling formula** is

$$\mathbb{P}(\mathbf{M}_n = \mathbf{m},\ K_n = k) = \frac{n!}{\alpha}\, \frac{\Gamma(\theta/\alpha + k)}{\Gamma(\theta/\alpha + 1)}\, \frac{\Gamma(\theta + 1)}{\Gamma(n + \theta)} \prod_{j=1}^n \frac{1}{m_j!}\Big(\frac{\alpha\, \Gamma(j - \alpha)}{j!\, \Gamma(1 - \alpha)}\Big)^{m_j}, \qquad \mathbf{m} \in A_{kn},$$

a Gibbs-type partition with $q_j = \alpha\Gamma(j - \alpha)/(j!\,\Gamma(1-\alpha))$ and $\sum_{j \ge 1} q_j = 1$. Here $K_n / n^{\alpha}$ converges almost surely to a Mittag-Leffler limit with density $g_\alpha$. Let $f : (0,1] \to \mathbb{R}$ satisfy $\int_0^1 y^{-\alpha-1} |f(y)|\, dy < \infty$ and $\mathbf{f}_n = (f(j/n))_{1 \le j \le n}$. For $x > 0$ let $Y_x^{(\nu, f)}$ be the infinitely divisible variable with characteristic function

$$\mathbb{E}\, e^{i\tau Y_x^{(\nu,f)}} = \exp\Big( \frac{\alpha x}{\Gamma(1-\alpha)} \int_0^1 (e^{i\tau y} - 1)\, e^{\nu f(y)}\, y^{-\alpha-1}\, dy \Big),$$

which has a continuous density $f_{Y_x^{(\nu,f)}}$, positive on $(0, \infty)$.

**Theorem (conditional local limit).** For every $\nu \in \mathbb{R}$ and $x > 0$,

$$\lim_{n\to\infty} n^{\alpha}\, \mathbb{E}\Big( e^{\nu \mathbf{f}_n^{\mathsf T}\mathbf{M}_n};\ K_n = \lfloor x n^\alpha \rfloor \Big) = \exp\Big( \frac{x\alpha}{\Gamma(1-\alpha)} \int_0^1 (e^{\nu f(y)} - 1)\, y^{-\alpha-1}\, dy \Big) \cdot \frac{f_{Y_x^{(\nu,f)}}(1)}{f_{Y_x^{(0)}}(1)} \cdot \frac{\alpha\, x^{\theta/\alpha}\, \Gamma(\theta)}{\Gamma(\theta/\alpha)}\, g_\alpha(x).$$

At $\nu = 0$ this is the local limit theorem $n^\alpha\, \mathbb{P}(K_n = \lfloor x n^\alpha \rfloor) \to \alpha x^{\theta/\alpha}\Gamma(\theta)\, g_\alpha(x) / \Gamma(\theta/\alpha)$.

**Consequences.**

1. *(Power functionals.)* For $p > \alpha$, conditionally on $K_n = \lfloor x n^\alpha \rfloor$, the mgf of $n^{-p}\sum_{j} j^p M_{jn}$ converges to $\frac{f_{Y_x^{(\nu,p)}}(1)}{f_{Y_x^{(0)}}(1)}\, \mathbb{E}\, e^{\nu T_x}$, where $T_x$ has the law of a stable subordinator with Lévy measure restricted to $(0,1]$: $\mathbb{E}\, e^{\nu T_x} = \exp\big( \frac{\alpha x}{p\,\Gamma(1-\alpha)} \int_0^1 (e^{\nu y} - 1)\, y^{-\alpha/p - 1}\, dy \big)$. The limit does not depend on $\theta$.
2. *(Counts of large blocks.)* For $0 < \lambda \le \mu \le 1$, the number $S_n^{\lambda,\mu} = \sum_{j = \lfloor \lambda n \rfloor}^{\lfloor \mu n \rfloor} M_{jn}$ of blocks with size between $\lambda n$ and $\mu n$ has, given $K_n = \lfloor x n^\alpha \rfloor$, a proper limiting distribution: a Poisson$\big(x\, c(\lambda,\mu)\big)$ weight with $c(\lambda,\mu) = (\lambda^{-\alpha} - \mu^{-\alpha})/\Gamma(1-\alpha)$, multiplied by a ratio of densities at $1$ of independent infinitely divisible sums.
3. *(Unconditional law.)* For $0 < \lambda < 1$ the number $S_n^{\lambda} = \sum_{j=\lfloor \lambda n \rfloor}^{n} M_{jn}$ of blocks of size at least $\lambda n$ converges in distribution to the mixed law

$$\lim_{n\to\infty} \mathbb{P}(S_n^\lambda = \ell) = \frac{c(\lambda)^\ell\, \Gamma(\theta)\, \Gamma(1-\alpha)^{\theta/\alpha + \ell}}{\Gamma(\theta/\alpha)\, \ell!} \int_0^\infty x^{\theta/\alpha + \ell - 1} e^{-x \lambda^{-\alpha}}\, f_{Y_x(\alpha,\lambda) + H_\ell(\lambda)}(1)\, dx, \qquad \ell = 0, 1, \dots,$$

with $c(\lambda) = (\lambda^{-\alpha} - 1)/\Gamma(1-\alpha)$ and $H_\ell(\lambda)$ a sum of $\ell$ i.i.d. variables with density proportional to $y^{-\alpha-1}$ on $(\lambda, 1]$; the right side is a probability mass function.

## Depends on

- [Moment generating function of the frequency spectrum of a Gibbs-type partition](moment-generating-function-of-the-frequency-spectrum-of-a-gibbs-type-partition.md)

## Expansion

Apply the Gibbs-type mgf representation with $\mathbf{u}_n = \mathbf{f}_n$ and $k = \lfloor x n^\alpha \rfloor$. Since $q_j \sim \alpha j^{-\alpha-1}/\Gamma(1-\alpha)$, the block-size variables scaled by $n$ form a triangular array whose row sums of $\lfloor x n^\alpha \rfloor$ terms converge to the infinitely divisible $Y_x^{(\nu,f)}$ with Lévy density $\frac{\alpha x}{\Gamma(1-\alpha)} e^{\nu f(y)} y^{-\alpha-1}$ on $(0,1]$; a local limit theorem gives $n\,\mathbb{P}(\sum_i \widehat X_i = n) \to f_{Y_x^{(\nu,f)}}(1)$, which produces the density ratio, and the tilt normalizer converges to the exponential prefactor. Choosing $f(y) = y^p$ or $f = \mathbf{1}_{[\lambda,\mu]}$ and inverting the mgf gives the corollaries; integrating the conditional law against the limiting law of $K_n/n^\alpha$ gives the unconditional limit.

## Sources

- Ross Arthur Maller, Soudabeh Shemehsavar, "Limit Theorems for the Pitman-Yor Frequency Spectrum", arXiv (2026). Theorem 3.1, Corollaries 3.1 and 3.2, Theorem 3.2, Lemmas 4.1–4.3. <https://doi.org/10.48550/arXiv.2607.23401>
