# Augmenting after a shortest augmentation (Hopcroft–Karp, Theorem 2)

Let $M$ be a matching of a simple graph $G$ on a finite vertex set, $p$ a shortest [$M$-augmenting walk](is-augmenting-walk.md), and $q$ a walk that is augmenting for the matching $M \oplus E(p)$. Then $|q| \ge |p| + |E(p) \cap E(q)|$, lengths counting edges.

In particular successive shortest augmenting paths never get shorter, and two of the same length are vertex-disjoint (Corollaries 3 and 4 of Hopcroft and Karp), which is what lets their algorithm augment along a maximal family of disjoint shortest paths in one phase.

## Informally uses

- [Disjoint augmenting paths in a symmetric difference (Hopcroft–Karp, Theorem 1)](exists-disjoint-augmenting-walks.md): applied to $M$ and $M \oplus E(p) \oplus E(q)$, which has two more edges.
- [Augmenting along a path (Hopcroft–Karp, Lemma 1)](symm-diff-is-matching.md)

## Sources

- J. E. Hopcroft and R. M. Karp, "An $n^{5/2}$ algorithm for maximum matchings in bipartite graphs", *SIAM Journal on Computing* 2(4) (1973), 225–231, §2. Theorem 2.
