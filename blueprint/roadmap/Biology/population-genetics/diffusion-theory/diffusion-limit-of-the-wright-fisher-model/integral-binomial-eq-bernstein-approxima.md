# One Wright–Fisher generation as a Bernstein approximation

For every natural number $M$, every continuous $f : \mathbb{R} \to \mathbb{R}$ and every $x \in [0, 1]$, if $X$ has the binomial distribution $\mathrm{Bin}(M, x)$, then $\mathbb{E}[f(X/M)]$, with the convention $k/0 = 0$, is the $M$-th Bernstein approximation $\sum_{k=0}^{M} f(k/M) \binom{M}{k} x^k (1 - x)^{M - k}$ of $f$ on $[0, 1]$, evaluated at $x$: the expected value of $f$ at the allele frequency after one Wright–Fisher generation with $M$ gene copies.
