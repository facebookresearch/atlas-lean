# Lucas numbers as binomial sums

Let $L_n$ denote the Lucas numbers. For every $r \ge 1$
and every natural number $n$,

$$L_{n+2r} = \sum_{k=0}^{n} \binom{n+r-1-k}{r-1} L_k +
\sum_{k=0}^{r-1} \binom{n+k}{k} L_{2(r-k)-1}$$

and

$$L_{n+2r} = \sum_{k=0}^{n} \binom{r+k-1}{k} L_{n-k} +
\sum_{k=0}^{r-1} \binom{n+k}{k} L_{2(r-k)-1}.$$

## Sources

- Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*, INTEGERS 24 (2024), Article A70, Corollary 2.
