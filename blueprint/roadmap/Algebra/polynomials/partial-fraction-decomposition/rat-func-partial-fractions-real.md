# Partial fraction decomposition over $\mathbb{R}$

For every real rational function
$f \in \mathbb{R}(X)$ there exist a polynomial $q \in \mathbb{R}[X]$, a finite set $S$ of monic
polynomials in $\mathbb{R}[X]$, each of degree $1$ or irreducible of degree $2$, and, for each
$p \in S$, a natural number $m_p$ and polynomials $g_{p,k} \in \mathbb{R}[X]$ for $k < m_p$, each
of degree less than the degree of $p$, such that, in $\mathbb{R}(X)$,

$$f = q + \sum_{p \in S} \sum_{k=0}^{m_p - 1} \frac{g_{p,k}}{p^{k+1}}.$$

Only existence is stated: the standard uniqueness of the decomposition (support and
multiplicities fixed by the denominator's irreducible factors) is not, so a witness may include
polynomials $p \in S$ with $m_p = 0$ or zero numerators $g_{p,k}$.

## Sources

- Field theory / `ℝ(X)`-partial fraction decomposition in `docs/undergrad.yaml`; S. Lang, Algebra, rev. 3rd ed., Springer, 2002, Ch. IV, §5 (Partial fractions), p. 187; https://en.wikipedia.org/wiki/Partial_fraction_decomposition#General_result
