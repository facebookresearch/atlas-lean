# Chen's Stirling expansion

Let $a(m, s)$, for natural numbers $m$ and $s$, be real
numbers satisfying $a(m, s + 1) = m \, a(m, s) - (m + 1) \, a(m + 1, s)$ for all $m$ and $s$.
Then for every natural number $t$,

$$a(0, t) = \sum_{m=0}^{t} (-1)^m \, m! \, S(t, m) \, a(m, 0),$$

where $S(t, m)$ is the Stirling number of the second kind.

This recurrence is a variant of the Akiyama–Tanigawa algorithm.

## Sources

- K.-W. Chen, "Algorithms for Bernoulli numbers and Euler numbers," Journal of Integer Sequences 4 (2001), Article 01.1.6, as stated in Dil, Kurt, and Cenkci (2007), Proposition 4. It is the `x = 0` case of `poly_initial_expansion`.
