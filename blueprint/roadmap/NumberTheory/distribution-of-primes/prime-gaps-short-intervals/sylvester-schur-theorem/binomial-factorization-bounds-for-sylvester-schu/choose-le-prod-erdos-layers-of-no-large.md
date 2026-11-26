# Erdős layer bound for binomial coefficients without large prime factors

Let $0 < N$ and
$r \le N$ be natural numbers such that every prime divisor of $\binom{N}{r}$ is at most $r$.
Write $P(m)$ for the product of all primes $p \le m$ and let $L = \lfloor \log_2 N \rfloor$. Then
$\binom{N}{r} \le \prod_{k=1}^{L} a_k$, where $a_1 = P(r)$ and $a_k = P(\lfloor N^{1/k} \rfloor)$
for $k \ge 2$.

This matches the product estimate in Erdős's proof.
