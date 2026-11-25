# Counting good outcomes of Shor period finding

Under the hypotheses of the Shor period-finding page ($N \ge 2$, $x$ a unit modulo $N$ of order $r$, $q = 2^L$ with $N^2 \le q < 2N^2$), fix $c_0 > 0$ and, for
each $d$ with $0 \le d < r$ and $\gcd(d, r) = 1$, let $c_d$ be an integer nearest to $dq/r$. If every outcome $(c_d, x^k \bmod N)$ with such $d$ and $0 \le k < r$ has
probability at least $c_0/r^2$, then with probability at least $c_0 \varphi(r)/r$ the measured $c$ is good for some $d$ with $\gcd(d, r) = 1$.

## Proof

$\lvert r c_d - d q \rvert = r \lvert c_d - dq/r \rvert \le r/2$, so $c_d$ is good for $d$. Consecutive values $dq/r$ are $q/r > N \ge 2$ apart, so the $c_d$ are distinct,
and the outcomes $(c_d, x^k \bmod N)$ for the $\varphi(r)$ values of $d$ and the $r$ values of $k$ are $\varphi(r) r$ distinct outcomes, since $x^k \bmod N$ are distinct for
$0 \le k < r$. Their probabilities sum to at least $\varphi(r) r \cdot c_0/r^2$.

## Related topics

- [Shor period finding: outcome distribution and order recovery](shor-period-finding-outcome-distribution-and-order-recovery.md)

## Sources

- P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer*, SIAM J. Computing 26(5) (1997); arXiv:quant-ph/9508027, Section 5 (for sufficiently large $n$, each state $\lvert c, x^k \rangle$ with $\lvert rc - dq \rvert \le r/2$ is observed with probability at least $1/(3r^2)$; the count of such states). <https://arxiv.org/abs/quant-ph/9508027>
