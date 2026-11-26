# Density of power-free values of integer polynomials

Let $f\in\mathbb Z[T]$ be irreducible over $\mathbb Q$, of degree $d\ge4$, and put $k=d-2$.
Write $r_f(q)$ for the number of residues $a\in\{0,\ldots,q-1\}$ with $q\mid f(a)$ and suppose
$r_f(p^k)<p^k$ for every prime $p$. The Euler product

$$
c_f=\prod_p\left(1-\frac{r_f(p^k)}{p^k}\right)
$$

converges as a product over finite prime subsets and is positive. For real $X\to+\infty$,

$$
\#\{1\le n\le\lfloor X\rfloor:\ p^k\nmid f(n)\text{ for every prime }p\}=c_f X+o(X).
$$

Negative values of $f(n)$ are counted by the same divisibility rule; zero is not counted. No
monicity, content, or coefficient-height assumption is added.

## Depends on

- [Power-free natural numbers](is-power-free.md)

## Expansion

Relate the integer divisibility test to the natural predicate through absolute value. Prove convergence and positivity of the Euler product from local root bounds, and separate the CRT finite-prime count from the required large prime-power divisor tail. Cover degree four through eight and the higher-degree part without silently restricting the polynomial class.

## Sources

- [PowerFreeValues.lean — `allDegrees`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PowerFreeValues.lean#L37-L43)
