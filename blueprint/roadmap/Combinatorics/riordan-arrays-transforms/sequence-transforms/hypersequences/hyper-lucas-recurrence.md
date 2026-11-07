# Recurrence for the hyperlucas numbers

Let $L^{(r)}_n$ denote the hyperlucas numbers,
the hypersequence of generation $r$ of the Lucas numbers. For all natural numbers $r$ and $n$,
$L^{(r)}_0 = 2$, $L^{(r)}_1 = 2r + 1$, and, in the rational numbers,

$$L^{(r+1)}_{n+2} = L^{(r+1)}_{n+1} + L^{(r+1)}_n + \frac{n + 2(r+1)}{n+2} \binom{n+r+1}{r}.$$

Equivalently, for $r \ge 1$,

$$L^{(r)}_{n+2} = L^{(r)}_{n+1} + L^{(r)}_n + \frac{n+2r}{n+2} \binom{n+r}{r-1}.$$

## Sources

- Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*, INTEGERS 24 (2024), Article A70, Theorem 6, Equation (2.13) (`integers-2024-A70-thm-6`).
