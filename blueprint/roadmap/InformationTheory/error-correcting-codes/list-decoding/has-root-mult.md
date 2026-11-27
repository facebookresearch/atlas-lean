# Root of multiplicity $r$

A bivariate polynomial $Q \in F[X][Y]$ has a root of multiplicity at least $r$ at $(a, b)$ if $Q$
lies in the $r$-th power of the [ideal of the point](point-ideal.md) $(X - a, Y - b)$.

Guruswami, Rudra and Sudan (Definitions 12.2.8 and 12.2.9) phrase this as: the translate
$Q(X + a, Y + b)$ has no monomial of total degree less than $r$. The two definitions agree, since
the translation is a ring automorphism carrying $(X - a, Y - b)$ to $(X, Y)$, and a polynomial lies
in $(X, Y)^r$ exactly when all its monomials have total degree at least $r$. The direction used
by the interpolation step is [the multiplicity criterion](has-root-mult-of-coeff.md). For $r = 1$ the condition is $Q(a, b) = 0$.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Definitions 12.2.8 and 12.2.9.
