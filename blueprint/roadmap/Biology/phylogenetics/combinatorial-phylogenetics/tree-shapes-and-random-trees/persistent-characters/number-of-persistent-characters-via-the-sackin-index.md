# Number of persistent characters via the Sackin index

**Setting.** Let $T$ be a rooted binary phylogenetic tree on $X=\{1,\dots,n\}$ with root $\rho$, augmented by a *root edge* $\rho'\rho$ whose extra endpoint $\rho'$ has state $0$. A binary character $f:X\to\{0,1\}$ is *persistent* on $T$ if some assignment of states to all vertices extending $f$ uses at most one $0\to1$ change followed by at most one $1\to0$ change (edges directed away from $\rho'$). Let $l(f,T)$ be the Fitch parsimony score of $f$ on $T$ (root edge ignored). The *Sackin index* is

$$ \mathcal S(T)=\sum_{u\ \text{inner}} n_u , $$

where $n_u$ is the number of leaves below the inner vertex $u$ (root included).

**Theorem.**

1. If $l(f,T)>2$ then $f$ is not persistent; if $l(f,T)\le 1$ then $f$ is persistent; for $l(f,T)=2$ persistence is decided by the two vertices that receive the union set $\{0,1\}$ in the first phase of the Fitch algorithm (one must be a non-adjacent ancestor of the other, with conditions on their Fitch sets). Each persistent character has a unique minimal persistent extension.
2. For $n\ge 2$, the number of persistent characters of parsimony score $2$ and the total number of persistent characters are

$$ \mathcal P_2(T)=2\,\mathcal S(T)-6n+8, \qquad \mathcal P(T)=2\,\mathcal S(T)-2n+4 . $$

3. Hence, among rooted binary trees with $n$ leaves, $\mathcal S(T_1)<\mathcal S(T_2)$ if and only if $\mathcal P(T_1)<\mathcal P(T_2)$: the more imbalanced the tree, the more persistent characters. The caterpillar, the unique maximizer of $\mathcal S$, has $n^2-n+2$ persistent characters, and in general

$$ 2n\lceil\log_2 n\rceil-2^{\lceil\log_2 n\rceil+1}+4 \le \mathcal P(T)\le n^2-n+2 . $$

## Depends on

- [Fitch's algorithm computes the small-parsimony score](../../../small-parsimony-problem/fitch-score-eq.md)

## Expansion

All $4n-4$ characters of score at most $1$ (the two constants and both colorings of each of the $2n-3$ edge splits of the unrooted tree, each realizable with a possible extra change on the root edge) are persistent. A persistent character of score $2$ is determined by its pair of Fitch union vertices: for every inner $u$ that is a non-adjacent ancestor of an inner $w$ there are exactly two such characters (the two pending subtrees of $w$ can swap states). An inner vertex $u$ has $n_u-2$ inner proper descendants, so there are $\sum_u (n_u-2)=\mathcal S(T)-2n+2$ ancestor pairs of inner vertices, of which $n-2$ are adjacent; this leaves $\mathcal S(T)-3n+4$ admissible pairs, and doubling and adding the $4n-4$ score-$\le1$ characters yields the formulas. The lower bound is the minimum Sackin index for $n$ leaves.

## Sources

- K. Wicke and M. Fischer, *Combinatorial views on persistent characters in phylogenetics*, arXiv:1802.02520 (2018). <https://doi.org/10.48550/arXiv.1802.02520> Theorem 1, Proposition 1, Theorem 2, Lemmas 5–6, Corollary 2 and Proposition 2 (Section 3). Published version: Advances in Applied Mathematics 119 (2020) 102046, <https://doi.org/10.1016/j.aam.2020.102046>.
