# The generalized Post correspondence problem is undecidable in every group containing a non-abelian free subgroup

For every finitely generated group $G$ that contains a non-abelian free subgroup, in particular every non-abelian free group of finite rank, the generalized Post correspondence problem $\mathrm{GPCP}(G)$ is undecidable.

1. If $F$ is a non-abelian free group of finite rank, $\mathrm{GPCP}(F)$ is undecidable.
2. If a finitely generated group $G$ contains a non-abelian free subgroup, then $\mathrm{GPCP}(G)$ is undecidable.
3. For a free group $F_n$ of rank $n \ge 32$, already $\mathrm{GPCP}_n(F_n)$, the problem with at most $n$ pairs, is undecidable.

These are corollaries in Section 4 of the source. Consequently $\mathrm{GPCP}$ is undecidable for non-elementary hyperbolic groups, non-abelian right-angled Artin groups, braid groups $B_n$ with $n \ge 3$, and non-virtually-solvable linear groups. By contrast, the source proves the homogeneous $\mathrm{PCP}$ decidable in polynomial time in every finitely generated nilpotent group.

## Depends on

- [Generalized Post correspondence problem for a group](generalized-post-correspondence-problem-for-a-group.md)
- [Group](../../../group-basics/group.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../word-problem-for-groups/novikov-unsolvable.md)

## Expansion

The hereditary word problem of a group $G$ asks, given a finite set $R$ of elements of $G$ and an element $w$, whether $w$ lies in the normal closure of $R$. A proposition of the source reduces the hereditary word problem of $G$ to $\mathrm{GPCP}(G)$, using the pairs $(r, 1)$ and $(x, x)$ to build up conjugates of relators. For a free group $F$ of rank at least two, the hereditary word problem contains the word problem of every finitely presented group with that many generators, and there are such groups with undecidable word problem. Decidability of $\mathrm{GPCP}$ passes to finitely generated subgroups, giving clause 2. For clause 3 the source uses Borisov's presentation with 4 generators and 12 relators, whose 16 symbols, doubled by inverses, give 32 pairs.

## Sources

- A. Myasnikov, A. Nikolaev and A. Ushakov, "The Post correspondence problem in groups", Journal of Group Theory 17 (2014), no. 6, 991–1008, https://doi.org/10.1515/jgth-2014-0022; read in arXiv:1310.5246v2 (the corollaries of Section 4 of arXiv:1310.5246v2, following the proposition that reduces the hereditary word problem to the generalized Post correspondence problem).
