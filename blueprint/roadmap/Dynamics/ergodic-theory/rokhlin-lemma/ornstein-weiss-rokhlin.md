# Ornstein–Weiss Rokhlin lemma for $\mathbb{Z}^d$-actions

Let $d \ge 1$, let $\Omega$ be a
standard Borel space with a probability measure $\mu$, and let $T$ assign to each
$v \in \mathbb{Z}^d$ a map $T_v \colon \Omega \to \Omega$ such that $T_0$ is the identity,
$T_{u + v} = T_u \circ T_v$ for all $u, v \in \mathbb{Z}^d$, every $T_v$ is measure preserving
for $\mu$, and the action is free (for every $v \ne 0$ the set of fixed points of $T_v$ has
$\mu$-measure zero). Then for every integer $N \ge 1$ and every $\varepsilon \in (0, \infty]$
there is a measurable set $B \subseteq \Omega$ such that the images $T_v(B)$, for $v$ in the
integer box $[0, N)^d$, are pairwise disjoint and their union has measure at least
$1 - \varepsilon$.

## Sources

- D. S. Ornstein and B. Weiss, *Entropy and isomorphism theorems for actions of amenable groups*, J. Anal. Math. 48 (1987), 1-141 — Theorem 5.2 establishes the multidimensional (and amenable-group) Rokhlin lemma. Listed as §109 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). No formalization found in any major prover. Problem `ornstein_weiss_rokhlin` of the lean-eval benchmark.
