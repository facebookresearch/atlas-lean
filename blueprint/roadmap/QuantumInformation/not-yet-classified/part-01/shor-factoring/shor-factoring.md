# Shor factoring

Shor's factoring theorem: there is a polynomial-time quantum algorithm that
factors integers. Precisely: there are polynomials `a` and `s`, a
polynomial-time gate generator `gates`, and a polynomial-time classical
post-processing function `post` such that, for every `N > 1`, running the
circuit `gates (Nat.bits N)` (of at most `s` gates, all well formed on the
working qubits) on the input state for `N` and measuring in the
computational basis yields, with probability at least `2 / 3`, an outcome
whose post-processed decoding is either a nontrivial factor of `N` or `0`
with `N` prime.

The input is `Nat.bits N`, the least-significant-bit-first binary expansion.
The gate model is the repo's `BQP` model: 2-local unitary gates with rational
entries, generated in polynomial time (Kitaev–Shen–Vyalyi / Arora–Barak).
The `2 / 3` is the success probability of the whole procedure, including the
standard internal repetition of order-finding; the circuit may repeat the
order-finding subroutine, which keeps its size polynomial. The classical
post-processing is the order-finding pipeline: continued fractions to recover
the order, `gcd` extraction of a factor, and a primality test (AKS). Its
`gcd` step is proved in this repo as `Cslib.Shor.gcd_factor_of_order` in
`CSLibExt/Algorithms/Quantum/Shor/OrderToFactor.lean`. The prevalence of
units satisfying that step's hypotheses is proved here only for `N = p * q`
with `p` and `q` distinct odd primes: `shor_good_units` in
`MathlibExt/Quantum/ShorGoodUnits.lean` shows that at least half of the units
modulo such an `N` have even order `r` and `a ^ (r / 2) ≠ -1`. The matching
bound for the other odd `N` with at least two distinct prime factors (three or
more distinct primes, or a repeated prime factor) is not formalized in this
repo. Even `N` and odd prime powers, including odd primes, need no such bound
and may have no good units at all (for an odd prime power the unit group is
cyclic, so `a ^ (r / 2) = -1` whenever `r` is even); the standard algorithm
settles them classically before order finding, with a parity check, a
perfect-power test, and the primality test.

## Sources

- P. W. Shor, Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer, SIAM J. Comput. 26 (1997), 1484–1509, Section 5; M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, Cambridge University Press, 2000, Section 5.3.
