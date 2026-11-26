# Robinson's definition of `ℤ` in `ℚ`

A rational number `N` is an integer if and only if
for all rationals `A` and `B`: if `2 + B Z² = X² + A Y²` has a rational solution `X, Y, Z`, and
for every rational `M` solvability of `2 + A B M² + B Z² = X² + A Y²` in rationals `X, Y, Z`
implies solvability of `2 + A B (M + 1)² + B Z² = X² + A Y²`, then
`2 + A B N² + B Z² = X² + A Y²` has a rational solution `X, Y, Z`.

This is the formula of J. Robinson, "Definability and decision problems in arithmetic",
J. Symbolic Logic 14 (1949), Theorem 3.1(i), pp. 106–107, transcribed clause by clause; part (ii)
of that theorem draws the consequence that `ℤ` is first-order definable in the field `ℚ`.

## Informally uses

- [Robinson's Lemma 3](robinson-lemma-3.md), for $A = 1$ and $B = p$ with $p \equiv 3 \pmod 4$: the rationals $M$ with $2 + pM^2 + pZ^2 = X^2 + Y^2$ solvable are those whose denominator is prime to $2$ and $p$, a set that contains $0$ and is closed under $M \mapsto M + 1$, so the denominator of $N$ is prime to $2$ and to every prime $p \equiv 3 \pmod 4$
- [Robinson's Lemma 4](robinson-lemma-4.md), for $A = q$ and $B = p$ with $p \equiv 1 \pmod 4$ and $q$ an odd prime with $\left(\frac{q}{p}\right) = -1$, which exists by Robinson's Lemma 5 (p. 108): in the same way the denominator of $N$ is prime to every prime $p \equiv 1 \pmod 4$
