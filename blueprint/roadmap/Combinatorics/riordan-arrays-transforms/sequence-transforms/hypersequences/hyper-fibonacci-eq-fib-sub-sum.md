# Hyperfibonacci numbers in terms of Fibonacci numbers

Let $F_k$ denote the $k$th Fibonacci
number and $F^{(r)}_n$ the hyperfibonacci numbers, given by $F^{(0)}_n = F_n$ and
$F^{(r+1)}_n = \sum_{k=0}^{n} F^{(r)}_k$. For all natural numbers $r$ and $n$,

$$F^{(r)}_n = F_{n+2r} - \sum_{k=0}^{r-1} \binom{n + k - 1}{k} F_{2(r-k)}.$$

## Sources

- Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*, INTEGERS 24 (2024), Article A70, Theorem 3, Equation (2.8).
