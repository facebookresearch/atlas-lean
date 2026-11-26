# Rising factorial generates Stirling numbers of the first kind

Let $R$ be a semiring and $n$ a natural number. Writing $c(n, k)$ for the unsigned Stirling
numbers of the first kind (the number of permutations of $n$ elements with exactly $k$ cycles),
the rising factorial is their generating polynomial: in the polynomial ring $R[X]$,

$$X (X + 1) \cdots (X + n - 1) = \sum_{k=0}^{n} c(n, k)\, X^k,$$

where the empty product for $n = 0$ is $1$.

## Sources

- Ronald L. Graham, Donald E. Knuth, and Oren Patashnik, *Concrete Mathematics: A Foundation for Computer Science*, 2nd ed., Addison-Wesley, 1994, Section 6.1.
