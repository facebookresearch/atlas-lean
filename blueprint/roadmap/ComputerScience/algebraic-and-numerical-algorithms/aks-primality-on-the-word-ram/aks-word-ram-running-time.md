# The AKS primality test runs in polylogarithmic word-RAM time

Consider the AKS procedure on input $n$: reject if $n < 2$ or $n$ is a perfect power; find the least $r \ge 2$ with $\gcd(r, n) = 1$ and $\mathrm{ord}_r(n) > (\log_2 n)^2$ (or with $1 < \gcd(r, n) < n$); reject if $1 < \gcd(a, n) < n$ for some $a \le r$; accept if $n \le r$; otherwise accept exactly when $(X + a)^n \equiv X^n + a$ in $(\mathbb{Z}/n\mathbb{Z})[X]/(X^r - 1)$ for all $1 \le a \le \lfloor \sqrt{\varphi(r)} \log_2 n \rfloor$.

There is a deterministic word-RAM program implementing this procedure that decides primality of $n$ (stored in one input word) in $(\log n)^{O(1)}$ instructions at every word size $w$ with $2^w > n^2 + n$; the instruction count is bounded by an explicit polynomial in $\log_2 n$.

## Proof sketch

Correctness is the AKS theorem. The search for $r$ stops at some $r \le \max\{3, \lceil \log_2 n \rceil^5\}$ by the small-modulus lemma, the gcd and totient loop costs $O(r \log n)$, and each congruence test costs $O(r^2 \log n)$ ring operations, with $O(\sqrt{r} \log n)$ tests.

## Depends on

- [PRIMES is in P](../../../TheoryOfComputation/polynomial-time-problems/aks-primality-test/primes-in-p.md)
- [Euler's totient function](../../../NumberTheory/arithmetic-functions/divisor-totient-functions/euler-totient.md)
- [Multiplicative order modulo $n$](../../../NumberTheory/congruences/congruences-modular-arithmetic/primitive-roots-modulo-prime-powers/mul-ord-mod.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
- [Perfect-power detection by integer roots](perfect-power-detection.md)
- [Arithmetic in the ring of polynomials modulo X^r - 1 and n](arithmetic-modulo-x-r-minus-one.md)

## Proof depends on

- [PRIMES is in P](../../../TheoryOfComputation/polynomial-time-problems/aks-primality-test/primes-in-p.md)
- [Existence of a small modulus of large order](small-modulus-of-large-order.md)
- [Polynomial Fermat congruence characterizes primes](polynomial-fermat-congruence.md)
- [Perfect-power detection by integer roots](perfect-power-detection.md)
- [Arithmetic in the ring of polynomials modulo X^r - 1 and n](arithmetic-modulo-x-r-minus-one.md)

## Sources

- M. Agrawal, N. Kayal and N. Saxena, "PRIMES is in P", Annals of Mathematics 160(2), 2004.
