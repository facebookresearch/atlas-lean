# The reduced comma digraph

For a base $b$, let $l(d, u)$ be the least $p > 0$ such that $b^k \bmod S_b(d, u) = b^{k+p} \bmod S_b(d, u)$ for all sufficiently large $k$, where $S_b(d, u)$ is the cycle sum of comma differences, and let $L$ be the least common multiple of $l(d, u)$ over $1 \le d < b$ and $u \in U(b, d) \cup \{0\}$, where $U(b, d)$ is the set of offsets of final terms in danger intervals (for $b \ge 2$, $1 \le d < b$ and $k > 2$, a final term is $d b^k - u$ with $u \in U(b, d)$; see the [characterization of final values in danger intervals](comma-danger-final-iff-mem.md)). A vertex $(d, u, \kappa)$ is valid when $1 \le d < b$, $u \in U(b, d)$ and $\kappa < L$. The digraph $G_b'$ has an edge from a valid $(d, u, \kappa)$ to a valid $(d', u', \kappa')$ when $d' = d + 1$ and $\kappa' = \kappa$ if $d < b - 1$, $d' = 1$ and $\kappa' = (\kappa + 1) \bmod L$ otherwise, and there is $K$ such that for every $k \ge K$ with $k \equiv \kappa \pmod L$ the comma map sends $(d, u, k)$ to $u'$.

## Sources

- R. Dougherty-Bliss and N. Ter-Saakov, The comma sequence is finite in other bases, J. Integer Seq. 28 (2025), Article 25.5.5.
