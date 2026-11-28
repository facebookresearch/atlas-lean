# Hilbert's product formula over $\mathbb{Q}$

Let $a$ and $b$ be nonzero rational
numbers. For a prime $p$, write $(a, b)_p$ for the $p$-adic Hilbert symbol of the images of $a$
and $b$ in $\mathbb{Q}_p$, and write $(a, b)_\infty$ for the real Hilbert symbol of their images
in $\mathbb{R}$. Then $(a, b)_p = 1$ for all but finitely many primes $p$, and

$$(a, b)_\infty \prod_p (a, b)_p = 1,$$

where the product runs over all primes $p$ and has only finitely many factors different
from $1$.

The symbols are defined through solvability of $a x^2 + b y^2 = 1$; by
`hilbertSymbol.eq_one_iff_exists_ternary_eq_zero` this agrees with the definition through
nontrivial zeros of $z^2 - a x^2 - b y^2$ used in the sources.

## Sources

- J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973, Chapter III, Theorem 3, as stated by J. S. Milne, *Class Field Theory*, version 4.03, 2020, Chapter III, Aside 4.2, p. 111: "It is defined also for $\mathbb{R}$, and Serre proves (Hilbert product formula) $\prod_{p \le \infty} (a, b)_p = 1$". The theorem number is as cited by E. Amerik and M. Verbitsky, *Construction of automorphisms of hyperkähler manifolds*, Compositio Math. 153 (2017), §3.
