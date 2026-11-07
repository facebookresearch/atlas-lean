# The Motzkin recurrence

`M(n + 1) = M(n) + ∑_{k < n} M(k) M(n - 1 - k)`, proved here
from the Catalan-weighted sum defining `motzkinNumber`. (Combinatorially, a Motzkin path of
length `n + 1` starts with a flat step, or with an up step whose matching down step splits the
rest into two shorter Motzkin paths; that path model is not formalized here.)

## Sources

- R. Donaghey and L. W. Shapiro, *Motzkin numbers*, Journal of Combinatorial Theory, Series A 23 (1977), 291–301.
