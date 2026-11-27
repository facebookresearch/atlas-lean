# Sampling residues by reducing uniform bit strings

Let $m \ge 1$ and $k \ge 0$, and let $x$ be a uniform integer in $\{0, \dots, 2^k - 1\}$ obtained from $k$ fair bits. Then the law of $x \bmod m$ is within statistical distance $m/2^k$ of the uniform distribution on $\mathbb{Z}_m$, and each residue has probability at least $\lfloor 2^k/m \rfloor / 2^k$. Taking $k = \lceil \log_2 m \rceil + n$ gives distance at most $2^{-n+1}$; this is how exponents in a group of order $q$ are drawn within statistical distance $2^{-n}$ of uniform from fair coins.

## Proof sketch

Write $2^k = am + r$ with $0 \le r < m$. Residues below $r$ have probability $(a+1)/2^k$ and the others $a/2^k$; the total variation from $1/m$ is $r(m-r)/(m 2^k) \le m/2^k$.

## Depends on

- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- D. E. Knuth, "The Art of Computer Programming, Volume 2: Seminumerical Algorithms", 3rd edition, Addison-Wesley, 1997.
