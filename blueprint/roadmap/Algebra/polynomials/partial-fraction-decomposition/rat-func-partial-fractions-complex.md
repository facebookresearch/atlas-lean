# Partial fraction decomposition over $\mathbb{C}$

For every complex rational function
$f \in \mathbb{C}(X)$ there exist a polynomial $q \in \mathbb{C}[X]$, a finite set $S$ of monic
polynomials of degree $1$ in $\mathbb{C}[X]$, and, for each $p \in S$, a natural number $m_p$
and polynomials $g_{p,k} \in \mathbb{C}[X]$ for $k < m_p$, each of degree less than the degree
of $p$, such that, in $\mathbb{C}(X)$,

$$f = q + \sum_{p \in S} \sum_{k=0}^{m_p - 1} \frac{g_{p,k}}{p^{k+1}}.$$

Only existence is stated: the standard uniqueness of the decomposition (support and
multiplicities fixed by the denominator's irreducible factors) is not, so a witness may include
polynomials $p \in S$ with $m_p = 0$ or zero numerators $g_{p,k}$.

## Sources

- S. Lang, Algebra, rev. 3rd ed., Springer, 2002, Ch. IV, §5 (Partial fractions), p. 187; https://en.wikipedia.org/wiki/Partial_fraction_decomposition#Statement
