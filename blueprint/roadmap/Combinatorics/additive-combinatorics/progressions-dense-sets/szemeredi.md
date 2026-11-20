# Szemerédi's theorem

For every natural number $k \ge 1$ and every real number $\delta > 0$
there is a natural number $N$ such that for every $n \ge N$, every set
$A \subseteq \{0, 1, \dots, n - 1\}$ with $\delta n \le |A|$ contains an arithmetic progression
of length $k$: there are natural numbers $a$ and $d > 0$ with $a + i d \in A$ for all $i < k$.

Proof: We derive the result from the density Hales–Jewett theorem by averaging coordinate-sum
translates and mapping combinatorial lines to arithmetic progressions.

## Background

- [Gowers's bound for Szemerédi's theorem](gowers-uniformity-norms/szemeredi-gowers-bound.md): the quantitative form, with a bound doubly exponential in $1/\delta$, from Gowers's Fourier-analytic proof.
- [Gowers uniformity norms](gowers-uniformity-norms/README.md): the norms that control counts of $k$-term progressions (the generalized von Neumann theorem), on which that proof rests.

## Sources

- Endre Szemerédi, "On sets of integers containing no $k$ elements in arithmetic progression", *Acta Arith.* 27 (1975), 199–245; the finitary density form above is equivalent to the statement that every set of positive upper density contains arbitrarily long arithmetic progressions.
