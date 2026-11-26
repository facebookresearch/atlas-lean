# Constrained dynamic programming for Robinson–Foulds supertrees

**Constrained problem.** Given source trees $\mathcal{T}$ on taxa $S = \bigcup_t L(t)$ and a set $X$ of
allowed bipartitions of $S$, find an unrooted binary tree $T$ minimizing
$\mathrm{RF}(T, \mathcal{T})$ subject to $\mathrm{Bip}(T) \subseteq X$. Let
$C = \{ A : [A, B] \in X \}$ be the set of allowed clades (both halves of every allowed
bipartition).

**Theorem (recursion).** Set $\mathrm{BPS}(\{s\}) = 0$ for $s \in S$, and for $A \in C$ with
$|A| \ge 2$ let $\mathrm{BPS}(A)$ be the maximum bipartition support from $\mathcal{T}$ over rooted
binary trees on $A$ all of whose clades lie in $C$. Then

$$\mathrm{BPS}(A) = \max\bigl\{ \mathrm{BPS}(A_1) + \mathrm{BPS}(A_2) + \mathrm{support}(A_1, A_2)
 : A = A_1 \cup A_2,\ A_1 \cap A_2 = \emptyset,\ A_1, A_2 \in C \bigr\}.$$

**Algorithm and complexity.** Compute $C$, sort it by cardinality, precompute
$\mathrm{support}(A_1, A_2)$ for disjoint allowed clades, fill $\mathrm{BPS}$ from small clades to
large, return $\mathrm{BPS}(S)$, recover an optimal rooted tree by backtracking, and unroot it. This
solves the constrained Robinson–Foulds supertree problem exactly in

$$O\bigl(|X|^2\, n\, k\bigr)$$

time for $n$ taxa and $k$ source trees.

## Depends on

- [Robinson–Foulds supertree as maximum bipartition support](robinson-foulds-supertree-as-maximum-bipartition-support.md)

## Expansion

The proof is by induction on $|A|$. In an optimal rooted tree on $A$, the two subtrees below the
root must themselves be optimal on their clades (otherwise swapping in a better subtree raises the
total, by the additive decomposition of support over nodes), so the optimum is at most the
right-hand side; conversely, any split $(A_1, A_2)$ of allowed clades combined with optimal subtrees
is feasible, so the optimum is at least it. By the observation that rooted and unrooted support
coincide, unrooting the optimal rooted tree on $S$ solves the unrooted constrained problem. The
algorithm has the same shape as ASTRAL's quartet dynamic program: the search space is restricted to
trees built from allowed clades, which can be taken from the source trees and from fast supertree
estimates, and within that space the optimum is found exactly rather than by heuristic tree search.

## Sources

- P. Vachaspati, T. Warnow, "FastRFS: fast and accurate Robinson-Foulds Supertrees using constrained
  exact optimization", Bioinformatics 33 (2017), Section 2.1, Theorem 2 (Eq. (1)) and
  Theorem 3, <https://doi.org/10.1093/bioinformatics/btw600> (PMC5870905).
