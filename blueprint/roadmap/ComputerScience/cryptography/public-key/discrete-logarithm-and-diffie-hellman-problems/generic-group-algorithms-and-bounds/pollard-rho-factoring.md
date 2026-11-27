# Pollard's rho factoring with Floyd cycle detection

Let $N$ be composite with a prime factor $p$, and iterate $x_{i+1} = f(x_i) \bmod N$ for a polynomial map $f$ (typically $x^2 + c$). Floyd's cycle detection compares $x_i$ and $x_{2i}$ and computes $\gcd(x_{2i} - x_i, N)$; it detects the first index $i \ge \mu$ that is a multiple of the cycle length $\lambda$ of the sequence modulo $p$, after at most $\mu + \lambda$ steps, each costing three evaluations of $f$ and one gcd. If the sequence modulo $p$ behaves like a random map, $\mu + \lambda = O(\sqrt{p})$ in expectation, giving a factor in $O(N^{1/4})$ steps.

## Proof sketch

Floyd's lemma: the sequences $x_i$ and $x_{2i}$ meet modulo $p$ at the least $i \ge \mu$ divisible by $\lambda$, which is at most $\mu + \lambda$. At that point $p$ divides the gcd; it is a proper factor unless the sequence also cycles modulo $N/p$ simultaneously.

## Depends on

- [Factoring experiment](../../hardness-assumptions/factor-game.md)

## Sources

- J. M. Pollard, "A Monte Carlo Method for Factorization", BIT Numerical Mathematics 15(3), 1975.
- D. E. Knuth, "The Art of Computer Programming, Volume 2: Seminumerical Algorithms", 3rd edition, Addison-Wesley, 1997.
