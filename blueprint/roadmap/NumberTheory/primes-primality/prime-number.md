# Prime number

A natural number $p$ is *prime* if it is irreducible in the multiplicative monoid of natural numbers: $p$ is not a unit, that is, $p \ne 1$, and whenever $p = ab$ with natural numbers $a$ and $b$, one of $a$ and $b$ is a unit, that is, equal to $1$. This excludes $1$, and also $0$, since $0 = 0 \cdot 0$. Equivalently, $p$ is prime if and only if $p \ge 2$ and the only natural numbers dividing $p$ are $1$ and $p$: a divisor $a$ of $p$ gives a factorisation $p = ab$, and a factorisation gives divisors. Thus the primes are the integers $p > 1$ whose only positive divisors are $1$ and $p$.

## Sources

- Kenneth Ireland and Michael Rosen, A Classical Introduction to Modern Number Theory, 2nd ed., Graduate Texts in Mathematics 84, Springer-Verlag, 1990.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for primes as irreducible natural numbers: `Nat.Prime`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Data/Nat/Prime/Defs.lean#L37-L42.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the characterisation by divisors: `Nat.prime_def`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Data/Nat/Prime/Defs.lean#L96-L97.
