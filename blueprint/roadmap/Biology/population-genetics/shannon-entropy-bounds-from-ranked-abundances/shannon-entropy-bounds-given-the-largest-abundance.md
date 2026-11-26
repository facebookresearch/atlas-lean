# Shannon entropy bounds given the largest abundance

Let $\mathbf p = (p_1, \dots, p_n)$ be a frequency vector with $p_1 \ge p_2 \ge \dots \ge p_n \ge 0$ and $\sum_i p_i = 1$ (relative abundances of $n$ species, or allele frequencies). Its **Shannon entropy** is

$$H(\mathbf p) = -\sum_{i=1}^n p_i \log p_i = \sum_{i=1}^n h(p_i), \qquad h(x) = -x \log x,\ h(0) = 0,$$

with the natural logarithm. Fix the largest frequency $p_1 \in [1/n, 1]$.

**Upper bound.** $H$ is maximized by $\mathbf p^{*} = \bigl(p_1, \tfrac{1-p_1}{n-1}, \dots, \tfrac{1-p_1}{n-1}\bigr)$, so

$$H(\mathbf p) \le H_{\max}(p_1, n) = h(p_1) + (n-1)\, h\!\left(\frac{1 - p_1}{n-1}\right).$$

**Lower bound.** $H$ is minimized by $\mathbf p^{**} = \bigl(p_1, \dots, p_1, 1 - (\lceil 1/p_1 \rceil - 1)p_1, 0, \dots, 0\bigr)$ with $\lceil 1/p_1 \rceil - 1$ entries equal to $p_1$, so

$$H(\mathbf p) \ge H_{\min}(p_1, n) = \bigl(\lceil 1/p_1 \rceil - 1\bigr) h(p_1) + h\bigl(1 - (\lceil 1/p_1 \rceil - 1) p_1\bigr).$$

For $p_1 \ge 1/2$ the minimizer is $(p_1, 1 - p_1, 0, \dots, 0)$. Both bounds decrease in $p_1$; the lower bound is piecewise, with breakpoints where $1/p_1$ is an integer, and does not depend on $n$ beyond its domain.

## Expansion

Shannon entropy is Schur-concave: if $\mathbf p$ is majorized by $\mathbf q$ then $H(\mathbf p) \ge H(\mathbf q)$. Among ordered vectors with first entry $p_1$, the vector spreading $1 - p_1$ evenly is majorized by all others and the vector concentrating $1 - p_1$ on as few entries as the ordering allows majorizes all others, which gives both bounds. The interval $[H_{\min}(p_1,n), H_{\max}(p_1,n)]$ is much narrower than $[0, \log n]$ when one class dominates, so the same entropy can mean very different communities: the abundance vectors $(0.5, 0.492, 0.001, \dots, 0.001)$ and $(0.85, 1/60, \dots, 1/60)$ with $n = 10$ both have $H \approx 0.75$, but only the second is pinned down by its dominant species.

## Sources

- M. L. Morrison and N. A. Rosenberg, "Mathematical bounds on Shannon entropy given the abundance of the ith most abundant taxon", *Journal of Mathematical Biology* 87 (2023), article 76, <https://doi.org/10.1007/s00285-023-01997-3> (PMC10603011; Equation (1) and Propositions 1 and 2, the latter restating Corollary 3.16 of Aw and Rosenberg (2018)).
