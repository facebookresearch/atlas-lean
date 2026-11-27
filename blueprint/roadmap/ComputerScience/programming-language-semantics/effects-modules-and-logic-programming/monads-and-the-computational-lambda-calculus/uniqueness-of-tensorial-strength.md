# Uniqueness of tensorial strength

Let $(T, \eta, \mu)$ be a monad over a category $\mathcal{C}$ with finite products and *enough points*: for $f, g : A \to B$, if $h ; f = h ; g$ for every $h : 1 \to A$ then $f = g$.
Then $(T, \eta, \mu, t)$ is a [strong monad](strong-monads.md) if and only if $t_{A,B}$ is the unique family of morphisms with

$$\langle a, b \rangle ; t_{A,B} = b ; T(\langle\, !_B ; a,\ \mathrm{id}_B \rangle)$$

for all points $a : 1 \to A$ and $b : 1 \to TB$, where $!_B : B \to 1$. So over such a category a monad has at most one strength.

## Depends on

- [Strong monads](strong-monads.md)

## Sources

- E. Moggi, "Notions of computation and monads", *Information and Computation* 93(1):55–92, 1991, <https://doi.org/10.1016/0890-5401(91)90052-4>: Section 3, Proposition 3.4 (uniqueness) and its proof.
