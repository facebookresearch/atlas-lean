# Recognizing finitely generated-by-cyclic groups is undecidable

No algorithm decides, from a finite presentation of a group with first Betti number $1$, whether the kernel of its map onto $\mathbb{Z}$ is finitely generated (or finitely presented, abelian, finite, or free); consequently the BNS invariant is not uniformly decidable.

A group with first Betti number $1$ has a unique normal subgroup $K$ with quotient $\mathbb{Z}$; for a property $\mathcal{P}$ of groups, it is $\mathcal{P}$-by-$\mathbb{Z}$ if $K$ has $\mathcal{P}$. Then (source):

1. for each property $\mathcal{P}$ among finitely generated, finitely presented, abelian, finite and free, no algorithm decides, on input a finite presentation of a group with Betti number $1$, whether it presents a $\mathcal{P}$-by-$\mathbb{Z}$ group (Theorem 5.3);
2. hence membership in the families of finitely presented-by-$\mathbb{Z}$ and of finitely generated-by-$\mathbb{Z}$ groups is undecidable (Corollary 5.4);
3. there is no algorithm that, given a finite presentation of a group $G$ with Betti number $1$ and a character $[\chi]$ in the character sphere $S(G)$, decides whether $[\chi]$ lies in the Bieri–Neumann–Strebel invariant $\Sigma^1(G)$ (Theorem 6.4).

## Depends on

- [Group](../../../group-basics/group.md)
- [Normal subgroup](../../../group-basics/normal-subgroup.md)
- [Quotient group by a normal subgroup](../../../group-basics/quotient-group.md)
- [Abelian group](../../../group-basics/abelian-group.md)
- [First Betti number of a group](../../../free-groups/automorphisms-of-free-groups/finite-index-subgroups-of-automorphism-groups-of/first-betti-rank.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../word-problem-for-groups/novikov-unsolvable.md)

## Expansion

If $K$ is a finitely presented perfect group, then $K * \mathbb{Z}$ has Betti number $1$ and its unique base group is a free product of infinitely many copies of $K$, which is finitely generated (finitely presented, abelian, finite, free) exactly when $K$ is trivial. An algorithm for clause 1 would therefore decide triviality of finitely presented perfect groups, after first checking that the abelianization is trivial, contradicting the Adian–Rabin theorem. Clause 3 follows because $G$ is finitely generated-by-$\mathbb{Z}$ exactly when both rank-one characters with kernel $K$ lie in $\Sigma^1(G)$.

## Sources

- B. Cavallo, J. Delgado, D. Kahrobaei and E. Ventura, "Algorithmic recognition of infinite cyclic extensions", Journal of Pure and Applied Algebra 221 (2017), no. 9, 2157–2179, https://doi.org/10.1016/j.jpaa.2016.10.008; read in arXiv:1509.05879v2 (Theorem 5.3, Corollary 5.4 and Theorem 6.4 of arXiv:1509.05879v2).
