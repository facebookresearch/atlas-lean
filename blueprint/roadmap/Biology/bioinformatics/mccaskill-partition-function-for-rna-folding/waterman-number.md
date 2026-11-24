# Waterman's recursion

For natural numbers $m$ and $n$, put $S_m(0) = 1$ and

$$S_m(n + 1) = S_m(n) + \sum_{k=m}^{n-1} S_m(k)\, S_m(n - 1 - k)$$

(Waterman 1978; Stein–Waterman 1979). For $m = 0$ these are the Motzkin numbers; for $m = 1$ the Stein–Waterman numbers $1, 1, 1, 2, 4, 8, 17, 37, \dots$.

## Sources

- M. S. Waterman, *Secondary structure of single-stranded nucleic acids*, Adv. Math. Suppl. Stud. 1 (1978), 167–212.
- P. R. Stein and M. S. Waterman, *On some new sequences generalizing the Catalan and Motzkin numbers*, Discrete Math. 26 (1979), 261–272.
