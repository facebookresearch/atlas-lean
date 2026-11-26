# Reconstruction from linearly many random $\pm 1$ queries

Let a database hold one secret sign $d_i \in \{\pm 1\}$ per row, $i \in [n]$, and let a $\pm 1$ query $v \in \{\pm1\}^n$ ask for $\langle v, d\rangle$. There are absolute constants $b, c > 0$ such that the following holds: draw $m \ge b n$ uniformly random $\pm 1$ queries; except with probability $e^{-cn}$ over the queries, for every mechanism whose answers all have error at most $\alpha\sqrt n$, the reconstruction that solves the linear program $\min_{y \in [-1,1]^n}\max_j |\langle v_j, y\rangle - a_j|$ and rounds to signs outputs a vector differing from $d$ in at most $c'\alpha^2 n$ positions for an absolute constant $c'$. Hence answering $O(n)$ random counting queries with error $o(\sqrt n)$ is blatantly non-private.

## Proof sketch

Any two vectors in $[-1,1]^n$ that both fit the answers have a difference $z$ with $|\langle v_j, z\rangle| \le 2\alpha\sqrt n$ for all queries; for random $\pm 1$ queries, every $z$ with many large coordinates has a constant fraction of queries with $|\langle v_j, z \rangle|$ larger than this, by anti-concentration and a net argument with a union bound.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Dinur–Nissim reconstruction attack](../differential-privacy/dinurnissim-reconstruction-attack.md)

## Sources

- Cynthia Dwork and Aaron Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science, 2014.
