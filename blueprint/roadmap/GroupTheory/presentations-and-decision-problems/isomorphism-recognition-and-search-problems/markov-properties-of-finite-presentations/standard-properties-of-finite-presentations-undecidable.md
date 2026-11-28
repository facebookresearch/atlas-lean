# Finiteness, abelianness, solvability, freeness and solvability of the word problem are undecidable for finite presentations

No algorithm decides, given a finite presentation, whether the presented group is finite, abelian, nilpotent, solvable, free or torsion-free, or whether it has solvable word problem.

**Theorem (Adian; Rabin).** Let $P$ be one of the following properties of groups: being finite, abelian, nilpotent, solvable, free or torsion-free, or having solvable word problem. Then there is no algorithm that decides, given a finite presentation, whether the group it presents has $P$.

Conventions: each property is considered separately, and the input is an arbitrary finite presentation. Being trivial is covered by the same argument; see the page on triviality.

## Depends on

- [Solvable word problem](../../word-problem-for-groups/word-problem-solvable.md)
- [Group](../../../group-basics/group.md)
- [Abelian group](../../../group-basics/abelian-group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Adian–Rabin theorem: Markov properties of finitely presented groups are undecidable](adian-rabin-theorem.md)
- [Novikov–Boone theorem (unsolvability of the word problem)](../../word-problem-for-groups/novikov-unsolvable.md)

## Expansion

Each listed property is a Markov property. It holds for the trivial group, and it is inherited by finitely generated subgroups, in particular by finitely presented ones: subgroups of finite, abelian, nilpotent, solvable or torsion-free groups have the same property, subgroups of free groups are free (the Nielsen–Schreier theorem), and a finitely generated subgroup of a group with solvable word problem has solvable word problem. So a finitely presented group without the property, for example a nonabelian free group of rank $2$ for finiteness, abelianness, nilpotency and solvability, the group $\mathbb{Z}/2$ for freeness and torsion-freeness, and a group with unsolvable word problem for the last property, embeds in no group with it. The Adian–Rabin theorem then applies.

## Sources

- Bjorn Poonen, *Undecidable problems: a sampler*, in: Interpreting Gödel: Critical Essays (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, https://doi.org/10.1017/CBO9780511756306.015, read in the copy arXiv:1204.0299v2, whose Section 6.4 ("Properties of groups") lists these properties as Markov properties because they are inherited by subgroups, so that each case is a special case of Theorem 6.2 there.
- Michael O. Rabin, *Recursive unsolvability of group theoretic problems*, Ann. of Math. (2) 67 (1958), no. 1, 172–194, https://doi.org/10.2307/1969933, cited beside the survey read above.
