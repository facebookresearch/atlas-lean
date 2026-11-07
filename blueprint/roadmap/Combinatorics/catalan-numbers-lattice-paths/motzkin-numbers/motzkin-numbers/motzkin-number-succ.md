# The Motzkin recurrence

`M(n + 1) = M(n) + ∑_{k < n} M(k) M(n - 1 - k)`. (Combinatorially, a Motzkin path of
length `n + 1` starts with a flat step, or with an up step whose matching down step splits the
rest into two shorter Motzkin paths.)

## Sources

- R. Donaghey and L. W. Shapiro, *Motzkin numbers*, Journal of Combinatorial Theory, Series A 23 (1977), 291–301.
