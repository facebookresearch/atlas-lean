# Weighted binomial sums of Lucas and Fibonacci numbers with even step

Let $F_m$ be the
Fibonacci numbers extended to all integers $m$ ($F_0 = 0$, $F_1 = 1$, $F_{m+2} = F_{m+1} + F_m$)
and $L_m = F_{m-1} + F_{m+1}$ the Lucas numbers. For every natural number $n$ and all integers
$k$, $r$ with $k$ even,

$$2 \sum_{j=0}^{n} j \binom{n}{j} L_{r+2kj} = 5 n L_k^{n-1} F_{r+nk} F_k + n L_k^n L_{r+nk}$$

and

$$2 \sum_{j=0}^{n} j \binom{n}{j} F_{r+2kj} = n L_k^{n-1} L_{r+nk} F_k + n L_k^n F_{r+nk}.$$

For $n = 0$ the exponent $n - 1$ is read as $0$; the term carrying it has the factor $n = 0$.

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Proposition 2 (`jis-2024-24.6.2-prop-2`).
