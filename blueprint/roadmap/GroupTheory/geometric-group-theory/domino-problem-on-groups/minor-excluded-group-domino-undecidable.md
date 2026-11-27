# A minor-excluded group has undecidable domino problem exactly when it is not virtually free

For a finitely generated group with a Cayley graph excluding the countable clique as a minor, the domino problem is undecidable exactly when the group is one-ended, or has infinitely many ends and a finitely generated one-ended planar subgroup, that is, exactly when the group is not virtually free.

A finitely generated group $\Gamma$ is $K_\infty$-minor-free if it has a finite generating set $S$ such that the Cayley graph $\mathrm{Cay}(\Gamma, S)$ does not contain the countable complete graph $K_\infty$ as a minor, and planar if some such Cayley graph is planar. Let $\Gamma$ be a finitely generated $K_\infty$-minor-free group. Then the domino problem is undecidable on $\Gamma$ if and only if

1. $\Gamma$ is one-ended, or
2. $\Gamma$ has infinitely many ends and has a finitely generated one-ended planar subgroup.

These two cases are exactly the cases in which $\Gamma$ is not virtually free (Theorem 5.8 of the source). So the conjecture of Ballier and Stein, that a finitely generated group has decidable domino problem if and only if it is virtually free, holds for $K_\infty$-minor-free groups, in particular for minor-excluded and for planar finitely generated groups.

## Depends on

- [Domino problem of a finitely generated group](domino-problem-of-a-group.md)
- [Group](../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The domino problem is undecidable on surface groups](domino-problem-undecidable-surface-groups.md)

## Expansion

Virtually free groups have decidable domino problem, a known result recalled in the introduction of the source. For the converse, let $\mathrm{Cay}(\Gamma, S)$ exclude $K_\infty$ as a minor. If $\Gamma$ is one-ended, Thomassen's theorem that a locally finite, transitive, non-planar, one-ended graph contains $K_\infty$ as a minor (Theorem 5.12, quoted) makes the Cayley graph planar; a one-ended planar group is a planar discontinuous group, which contains the fundamental group of a closed orientable surface of genus $g \ge 1$ as a subgroup of finite index (Theorem 5.9, quoted); that surface group has undecidable domino problem (Theorem 5.10, quoted), and undecidability passes from a finitely generated subgroup to the whole group. If $\Gamma$ has infinitely many ends and is not virtually free, it is accessible, since the source proves that finitely generated $K_\infty$-minor-free groups are accessible (Corollary 1.5), so by the Karrass–Pietrowski–Solitar characterization of virtually free groups (Theorem 2.5, quoted) some vertex group of its finite graph of groups with finite edge groups is one-ended; by Babai's theorem (Theorem 5.11, quoted) that vertex group has a Cayley graph that is a minor of $\mathrm{Cay}(\Gamma, S)$, hence $K_\infty$-minor-free, and the one-ended case applies. Groups with $0$ or $2$ ends are finite or virtually $\mathbb{Z}$ and have decidable domino problem.

## Sources

- L. Esperet, U. Giocanti and C. Legrand-Duchesne, "The structure of quasi-transitive graphs avoiding a minor with applications to the domino problem", Journal of Combinatorial Theory, Series B 169 (2024), 561–613, https://doi.org/10.1016/j.jctb.2024.08.002; arXiv:2304.01823v4 (Theorem 5.8 and its proof, with Corollary 1.5, the quoted Theorem 2.5 and the quoted Theorems 5.9 to 5.12, of arXiv:2304.01823v4).
