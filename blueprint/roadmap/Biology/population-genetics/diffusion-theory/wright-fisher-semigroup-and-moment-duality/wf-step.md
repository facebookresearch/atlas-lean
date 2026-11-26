# One generation of the neutral Wright–Fisher chain

For a natural number $M$, the operator $W_M$ on the continuous real functions on $[0, 1]$ given by

$$(W_M f)(x) = \sum_{k=0}^{M} f\Bigl(\frac{k}{M}\Bigr) \binom{M}{k} x^k (1 - x)^{M - k},$$

the $M$-th Bernstein operator, with the convention $k/0 = 0$ (so $W_0 f$ is the constant $f(0)$). For $M \ge 1$, $(W_M f)(x)$ is the expected value of $f$ at the next allele frequency $X/M$, where $X$ has the binomial distribution $\mathrm{Bin}(M, x)$: one generation of the neutral Wright–Fisher chain with $M$ gene copies. It is a linear operator of norm at most $1$ for the sup norm.
