# Lucas-type recursion for 1-metered parking functions

Write $\mathrm{mpf}_{m,n}(1)$ for
the number of $1$-metered $(m, n)$-parking functions. For every natural number $n$,
$\mathrm{mpf}_{1,n}(1) = n$ and $\mathrm{mpf}_{0,n}(1) = 1$, and for every natural number $m$
with $1 \le m \le n$,

$$\mathrm{mpf}_{m+1,n}(1) = n \cdot \mathrm{mpf}_{m,n}(1) - \mathrm{mpf}_{m-1,n}(1),$$

where the subtraction is taken in the integers.

## Sources

- Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking Functions*, INTEGERS 25 (2025), Article A73, Theorem 2 (`integers-2025-A73-thm-2`).
