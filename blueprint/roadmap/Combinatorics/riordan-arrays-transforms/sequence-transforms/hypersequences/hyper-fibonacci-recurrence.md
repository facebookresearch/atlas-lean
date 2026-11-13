# Recurrence for the hyperfibonacci numbers

Let $F^{(r)}_n$ denote the hyperfibonacci
numbers. For all natural numbers $r$ and $n$, $F^{(r)}_0 = 0$, $F^{(r)}_1 = 1$, and
$F^{(r+1)}_{n+2} = F^{(r+1)}_{n+1} + F^{(r+1)}_n + \binom{n+r+1}{r}$.

Equivalently, for $r \ge 1$, $F^{(r)}_{n+2} = F^{(r)}_{n+1} + F^{(r)}_n + \binom{n+r}{r-1}$, the
form in which Parisse quotes this result of Cristea, Martinjak and Urbiha.

## Sources

- Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*, INTEGERS 24 (2024), Article A70, Theorem 4, Equation (2.9).
