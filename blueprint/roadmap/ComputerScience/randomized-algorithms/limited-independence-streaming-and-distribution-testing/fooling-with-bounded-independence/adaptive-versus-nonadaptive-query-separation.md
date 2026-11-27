# Adaptive t-query tests separate a law with almost uniform t-bit marginals

For every integer $t \ge 1$ there is a distribution $Z$ on $n = t - 1 + 2^{t-1}$ bits such that every marginal of $Z$ on $t$ fixed coordinates is within total variation distance $t/2^t$ of uniform, yet some decision tree of depth $t$ accepts every sample of $Z$ and accepts a uniform string with probability exactly $1/2$. So an adaptive $t$-query test can have distinguishing gap $1/2 = (2^{t-1}/t) \cdot (t/2^t)$: the factor $2^t$ in the adaptive bound for almost $t$-wise independence cannot be replaced by anything smaller than $2^{t-1}/t$.

## Proof sketch

Split the coordinates into $t - 1$ address bits $a$ and $2^{t-1}$ data bits indexed by addresses. Let $Z$ be a uniform string $U$ with the data bit at address $a$ overwritten by $0$. The tree reads the address and then that data bit, accepting iff it is $0$: it accepts every sample of $Z$ and a uniform string with probability $1/2$. For a fixed set of $t$ coordinates containing $j$ data bits, $Z$ and $U$ differ on these coordinates only if the address points to one of them and that bit of $U$ is $1$, an event of probability at most $j \cdot 2^{-(t-1)} \cdot \frac12 \le t/2^t$; the coupling bounds the total variation distance.

## Depends on

- [Adaptive bit tests of almost t-wise independent distributions](adaptive-tests-of-almost-t-wise-independence.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
