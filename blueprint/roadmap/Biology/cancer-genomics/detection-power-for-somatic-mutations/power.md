# Power of the randomized mutation detection test

For a natural number $n$ and reals $p_0, \mathrm{FPR}, f$, the power is

$$\mathrm{Pow}(n, f) = P_f(k) + d\, B(k - 1 \mid n, f),$$

where $k$ is the [critical count](critical-count.md), $d$ the [randomization probability](randomization.md), $P_f$ the [upper tail](upper-tail.md), $B$ the [binomial probability](binom-pmf.md) and $k - 1$ is truncated at $0$. For $0 \le p_0 \le 1$, $0 \le \mathrm{FPR} < 1$ and $0 \le f \le 1$, it is the probability that the test rejects for a count $X$ with the binomial distribution $\mathrm{Bin}(n, f)$: the test rejects when $X \ge k$, and with probability $d$ when $X = k - 1$ (Carter et al. 2012, Eq. 9, with the randomization at $k - 1$).
