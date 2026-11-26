# Expected extinction time of the oldest allele

**Setting.** Let $\theta > 0$ and let $\hat Z$ be the diffusion on $[0,1]$ with generator
$$\hat G f(x) = x(1-x) f''(x) - \theta x f'(x),$$
the diffusive limit of the frequency of the oldest allele in the age-ordered infinitely-many-neutral-alleles Moran model, run until that allele dies out. Let $\tau = \inf\{t : \hat Z(t) = 0\}$.

**Proposition.** Let $g_0$ be the unique solution in $C([0,1]) \cap C^2((0,1])$ of $\hat G g_0 = -1$ with $g_0(0) = 0$ and $g_0'(1)$ finite. Then $\mathbb{E}_x[\tau] = g_0(x)$ for every $x \in [0,1]$, explicitly
$$\mathbb{E}_x[\tau] = \int_0^x (1-u)^{-\theta} \left[\int_u^1 \frac{(1-y)^{\theta-1}}{y}\, dy\right] du.$$
There are constants $c_1, c_2, c_3 > 0$ such that on $(0,1)$
$$0 < g_0'(x) \le c_1 (1 - \ln x), \qquad |g_0''(x)| \le c_2\, x^{-1}, \qquad |g_0^{(3)}(x)| \le c_3\, x^{-2},$$
and $g_0$ is strictly concave on some interval $(0, \delta)$.

**Convergence of extinction times.** If the rescaled discrete oldest-allele chains $\tilde Z^n$ (count divided by $n$, time sped up by $\alpha_n = (n+\theta)(n+1)$) satisfy $\tilde Z^n(0) \Rightarrow \hat Z(0)$, then $(\tilde Z^n, \tilde \tau_n) \Rightarrow (\hat Z, \tau)$ in $D_{[0,1]}[0,\infty) \times [0,\infty]$, where $\tilde\tau_n$ is the first hitting time of $0$.

## Depends on

- [Oldest-allele frequency is Markov in the age-ordered Moran model](oldest-allele-frequency-is-markov-in-the-age-ordered-moran-model.md)

## Expansion

The equation $x(1-x) g'' - \theta x g' = -1$ is first order in $g'$; the integrating factor $(1-x)^{-\theta}$ gives $g'(u) = (1-u)^{-\theta}\int_u^1 (1-y)^{\theta-1} y^{-1}\, dy$, the integration constant fixed so that $g'$ stays finite at $1$. The logarithmic singularity of $g_0'$ at $0$ comes from the factor $1/y$; the derivative bounds feed the uniform generator convergence (Ethier–Kurtz style) that transfers hitting times to the limit.

## Sources

- Douglas Rizzolo and Marydol Soto-Santarriaga, "The Oldest Allele in a Moran Model", arXiv:2608.23450 (2026), Theorem 4, Proposition 6 and Corollary 1, <https://doi.org/10.48550/arXiv.2608.23450>.
