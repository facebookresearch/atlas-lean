# Amortized cost of a splay is at most $3 \log_2 n + 1$

For every key $x$ and every binary tree $t$ with $n$ nodes over a linear order (with
$\log_2 0$ taken to be $0$),

$$\mathrm{cost}(x, t) + \Phi(S_x(t)) - \Phi(t) \le 3 \log_2 n + 1.$$

This is the [access lemma](access-lemma.md) with the term $-3\log_2 |\mathrm{focus}(x, t)|$
dropped, since that subtree has at least one node when $t$ is nonempty (and the bound reads
$1 \le 1$ for the empty tree).

## Informally uses

- [Access lemma for splay trees (unit weights)](access-lemma.md): drop the nonpositive term.

## Sources

- D. D. Sleator and R. E. Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985)
  652–686, §2, proof of Theorem 1 (with weights $1/n$ there, which give the same ranks up to the
  additive constant $\log_2 n$).
