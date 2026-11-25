# Nonzero polynomials over nondiscrete fields have Haar-null zero sets

Let $F$ be a non-discrete, locally compact, second-countable Hausdorff topological field with its
Borel $\sigma$-algebra, $\iota$ a finite set, $p \ne 0$ a polynomial over $F$ in the variables
$(X_i)_{i \in \iota}$, and $\mu$ an additive Haar measure on $F^\iota$. Then
$\mu\{x \in F^\iota : p(x) = 0\} = 0$.

## Idea

For $F = \mathbb{R}$ and Lebesgue measure, a nonzero polynomial vanishes only on a null set, so a
property defined by $p(x) \ne 0$, such as the invertibility of a matrix with $p = \det$, holds
almost everywhere. The proof is by induction on the number of variables: write $p$ as a polynomial
in the last variable whose coefficients are polynomials in the others; outside the null zero set of
a nonzero coefficient, $p$ is a nonzero polynomial in the last variable with finitely many roots,
points are null because the field is not discrete, and Fubini's theorem concludes.

## Statements

- [Nonzero polynomials over nondiscrete fields have Haar-null zero sets](measure-set-of-eval-eq-zero-of-ne-zero.md)
