# Cramér's decomposition theorem

Let $X$ and $Y$ be measurable real random variables on a probability space. If $X$ and $Y$ are independent and $X + Y$ has a Gaussian law, then $X$ and $Y$ each have a Gaussian law. Here a Gaussian law may be degenerate, that is, a point mass.

## Idea

Sums of independent Gaussian variables are Gaussian; Cramér's theorem is the converse, so a normal law cannot be split into independent summands that are not normal. The proof is analytic. The characteristic function of $X + Y$ is $e^{iat - \sigma^2 t^2 / 2}$, which extends to an entire function without zeros. Because the tails of $X$ and $Y$ are controlled by those of $X + Y$, their characteristic functions also extend to entire functions; they have no zeros, since their product has none, and they grow at most like $e^{c|z|^2}$. Hadamard's factorization theorem then makes each of them the exponential of a polynomial of degree at most $2$, which is the characteristic function of a possibly degenerate Gaussian law. Raikov proved the analogous statement for the Poisson law.

## Statements

- [Cramér's decomposition theorem](cramer-decomposition.md)

## Sources

- H. Cramér, *Über eine Eigenschaft der normalen Verteilungsfunktion*, Mathematische Zeitschrift (1936).
