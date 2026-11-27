# Shor success budget after approximation and repetition

This node collects the success-probability budget of Shor's factoring algorithm on its different input branches.

## Expansion

A sound expansion has separate pages for:

1. **Quantities.** For an odd composite $N$ that is not a prime power: an explicit lower bound $\tau(N) > 0$, computable
   from $N$, with $\varphi(r)/r \ge \tau(N)$ for every $3 \le r < N$ (an effective form of $\varphi(r)/r > \delta/\log\log r$); the
   effective per-run constant $c_0$ and threshold $N_0$, such that for $N \ge N_0$ one period-finding run returns the order
   $r$ of the chosen unit with probability at least $c_0\,\varphi(r)/r$; and $\delta(N)$, the total circuit and approximation
   error per round. A random unit has even order $r$ with $x^{r/2} \not\equiv -1 \pmod N$ with probability at least $1/2$.
2. **Repetition budget.** If each round succeeds with probability at least $p(N) \ge (c_0\tau(N) - \delta(N))/2$, the factor
   $1/2$ being the good-unit probability, and $\delta(N) \le c_0\tau(N)/4$, then $\lceil 4/(c_0 \tau(N)) \rceil$ independent
   rounds, a number computable from $N$ alone and of order $\log\log N$ when $\tau(N)$ is of order $1/\log\log N$, all fail
   with probability at most $e^{-3/2} < 0.224$; any error not included in $\delta(N)$ must fit in the remaining slack below
   $1/3$.
3. **Other branches.** Even $N$, prime powers and primes are handled before period finding, inputs $N < N_0$ by trial
   division or a fixed table, and units of order $1$ or $2$ inside the effective constants. Every candidate order and factor
   is checked classically and output $0$ means that $N$ is prime, so these branches contribute no error.
4. **Conclusion.** The whole procedure is correct with probability at least $2/3$ for every $N > 1$.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Proof prerequisite: Success stability of phase estimation/period finding under approximate gates.
- Proof prerequisite: Non-asymptotic Shor per-outcome bound with explicit constant $c_0$ and threshold $N_0$.
- Statement prerequisite: Effective lower bound for $\varphi(r)/r$ valid for all $r \ge 3$.

## Proof depends on

- [Most units give a factor in Shor's reduction](shor-s-reduction-of-factoring-to-order-finding/card-units-good-for-factoring-ge.md)
- [BQP error reduction](../../TheoryOfComputation/randomized-and-quantum-complexity/bqp-error-reduction.md)

## Sources

- P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer*, arXiv:quant-ph/9508027v2 (SIAM J. Comput. 26 (1997)), Section 5 (the order is obtained with probability at least $\varphi(r)/3r$; with $\varphi(r)/r > \delta/\log\log r$, Hardy and Wright, Theorem 328, as cited there, $O(\log\log r)$ repetitions suffice; the reduction works for odd $n$ that are not prime powers). <https://arxiv.org/abs/quant-ph/9508027>
