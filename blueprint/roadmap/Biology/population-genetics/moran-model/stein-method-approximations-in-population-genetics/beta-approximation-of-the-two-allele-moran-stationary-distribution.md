# Beta approximation of the two-allele Moran stationary distribution with rate 1/n

**Model.** Ewens' two-allele Moran chain on $\{0, 1, \dots, 2n\}$ counts copies of one allele, with mutation probabilities $u$ (away from it) and $v$ (toward it), $0 \le u, v \le 1$:

$$p(i, i-1) = \frac{i(2n-i)(1-v) + u\,i^2}{(2n)^2}, \qquad p(i, i+1) = \frac{i(2n-i)(1-u) + v(2n-i)^2}{(2n)^2},$$

and $p(i,i) = 1 - p(i,i-1) - p(i,i+1)$. Its stationary law $\pi$ has an exact but unwieldy gamma-function formula. Let $I \sim \pi$, $W = I/(2n)$, and scale mutation as $v = a/(2n)$, $u = b/(2n)$ with $a, b > 0$ fixed. Ewens showed $W$ is approximately Beta$(a,b)$. Distances are measured in the smooth metric

$$d_2(X,Y) = \sup_{h \in H_2}|\mathbb{E}h(X) - \mathbb{E}h(Y)|,$$

with $H_2$ the differentiable $h$ whose derivative is Lipschitz and $\|h'\|_\infty, \|h''\|_\infty \le 1$.

**Theorem.**
1. $\mathbb{E}W = \frac{a}{a+b}$ and $\mathrm{Var}(W) = \frac{2abn}{(a+b)^2\big(2n + a(2n-1) + b(2n-1)\big)}$.
2. (*Upper bound.*) $d_2\big(W, \mathrm{Beta}(a,b)\big) \le K(a,b)/n$ with the explicit constant

$$K(a,b) = \frac{(9a + 6b)\,C(a,b) + C(a+1,b+1) + (a+b)\,C(a+1,b+1)\,C(a,b)}{12},$$

where $C(\cdot,\cdot)$ are Döbler's Beta–Stein constants (e.g. $C(a,a) = 4$ for $0 < a < 1$ and $C(a,a) = 2a\sqrt\pi\,\Gamma(a)/\Gamma(a + 1/2)$ for $a \ge 1$).
3. (*Lower bound.*) $d_2\big(W, \mathrm{Beta}(a,b)\big) \ge \frac{ab}{4n(a+b)(1+a+b)^2}$.

Hence the rate $1/n$ is sharp.

## Expansion

Run the stationary chain one step to get an exchangeable pair $(W, W')$. With $\lambda = 1/(4n^2)$ it satisfies Döbler's conditions for Beta approximation: $\frac1\lambda\mathbb{E}[W' - W \mid W] = (a+b)\big(\frac{a}{a+b} - W\big)$ exactly, and $\frac{1}{2\lambda}\mathbb{E}[(W'-W)^2 \mid W] = W(1-W) + S$ with a remainder $S = O(1/n)$; Döbler's theorem bounds $d_2$ by $C(a,b)\,\mathbb{E}|S|$ plus a multiple of $\mathbb{E}|W'-W|^3/\lambda$, both $O(1/n)$. The mean and variance follow from the same linear regression identity; the exact variance differs from the Beta variance $ab/((a+b)^2(a+b+1))$ at order $1/n$, which is what prevents a faster rate.

## Sources

- Jason Fulman, "Beta approximation for the two alleles Moran model by Stein’s method", *Statistics & Probability Letters* 208 (2024), 110051, <https://doi.org/10.1016/j.spl.2024.110051>. Numbering as in the preprint arXiv:2307.13835v1, <https://arxiv.org/abs/2307.13835v1>: Theorem 1.1, Theorem 2.1 (Döbler), Corollary 2.3 and Proposition 2.4.
