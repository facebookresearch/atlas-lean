# The threshold constant $k_0$ in the Bennett–Siksek theorem

A natural number $k_0$, to
be supplied: the absolute constant from which Theorem 2 holds, that is, for every natural
number $k \ge k_0$, every solution in integers $n$, $d$, $y$ and a prime natural number $l$ of
$\prod_{i=0}^{k-1} (n + i d) = y^l$ with $\gcd(n, d) = 1$ has $y = 0$ or $d = 0$ or
$l \le \exp(10^k)$.

The source requires $k_0$ to be effectively computable; the formal statement does not enforce
this.

## Sources

- M. Bennett and S. Siksek, `A conjecture of Erdős, supersingular primes and short character sums`, Annals of Math, 191 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-191-2-ErdosSupersingularPrimes.lean Via leanprover/lean-eval@38361be, problem `annals_erdos_supersingular_primes`.
