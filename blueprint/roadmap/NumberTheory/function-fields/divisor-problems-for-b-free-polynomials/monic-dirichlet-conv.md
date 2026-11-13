# Dirichlet convolution over monic divisors

Let $F$ be a field. The Dirichlet convolution
of functions $\alpha$ and $\beta$ from $F[T]$ to $\mathbb{C}$ is the function $\alpha * \beta$
given at $f \in F[T]$ by

$$(\alpha * \beta)(f) = \sum_{g \text{ monic},\ g \mid f} \alpha(g)\, \beta(f/g),$$

the sum running over the monic divisors $g$ of $f$.

When $f = 0$ every monic polynomial divides $f$; the sum is then the sum of its nonzero terms if
there are finitely many, and $0$ otherwise.

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of the Dirichlet convolution.
