# Covering a target set with few pairwise independent hash functions

Let $h : \iota \times X \to Y$ be pairwise independent with uniform seed, $Y$ nonempty, and $S \subseteq X$ finite. If $q|Y| \le |S|$ and $|Y| < q^p$ for integers $q, p$, then there are seeds $i_1, \dots, i_p$ such that $Y = \bigcup_{j \le p} h_{i_j}(S)$. Conversely, if $p$ functions cover $Y$ from $S$ then $|Y| \le p|S|$. This two-sided size test underlies Lautemann-style and set-size estimation arguments.

## Proof sketch

For a fixed target $y$ the number of points of $S$ mapped to $y$ has mean $|S|/|Y| \ge q$ and variance at most its mean, so $y$ is missed with probability at most $1/q$. With $p$ independent seeds, $y$ is missed by all with probability at most $q^{-p} < 1/|Y|$, and a union bound over targets finds a good tuple.

## Depends on

- [Pairwise independent samples hit dense sets](pairwise-independent-samples-hit-dense-sets.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- S. Goldwasser and M. Sipser, "Private Coins versus Public Coins in Interactive Proof Systems", Proceedings of the 18th ACM Symposium on Theory of Computing, 1986.
