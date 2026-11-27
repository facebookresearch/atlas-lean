# The isomorphism and commensurability problems are independent for classes of finite presentations

There is a recursively enumerable class of finite presentations, with uniformly solvable word problem, in which isomorphism is decidable but commensurability is not; and there is one in which commensurability is decidable but isomorphism is not.

Two groups are commensurable if they have isomorphic subgroups of finite index. For a class $\mathcal{C}$ of finite presentations, the isomorphism (commensurability) problem within $\mathcal{C}$ asks for an algorithm that decides, given two presentations from $\mathcal{C}$, whether the groups they define are isomorphic (commensurable). Then (source):

1. there is a recursively enumerable class $\mathcal{C}_1$ of finite presentations of groups, with uniformly solvable word problem, such that the isomorphism problem is solvable but the commensurability problem is unsolvable within $\mathcal{C}_1$ (Theorem 1.1);
2. there is a recursively enumerable class $\mathcal{C}_2$ of finite presentations of groups such that the commensurability problem is solvable but the isomorphism problem is unsolvable within $\mathcal{C}_2$ (Theorem 1.2).

Within the class of all finite presentations, both problems are unsolvable, as are the virtual isomorphism, quasi-isometry and bi-Lipschitz equivalence problems (Lemma 6.1).

## Depends on

- [Group](../../../group-basics/group.md)
- [Solvable word problem](../../word-problem-for-groups/word-problem-solvable.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../word-problem-for-groups/novikov-unsolvable.md)

## Expansion

The constructions use NFQ groups (groups whose only finite quotient is trivial) with trivial center. For the first, the source constructs such a group $A_1$ with solvable word problem and a recursively enumerable set of words whose torsion problem in $A_1$ is unsolvable (Proposition 3.2); for the second, a group $A_2$ and a recursively enumerable set of elements of order at most two whose word problem in $A_2$ is unsolvable (Proposition 3.3). Encoding the words $z_i$ into a recursive family of finite presentations built from $A_1$, respectively $A_2$, makes commensurability, respectively isomorphism, of members of the family equivalent to the undecidable question while keeping the other problem decidable.

## Sources

- G. Arzhantseva, J.-F. Lafont and A. Minasyan, "Isomorphism versus commensurability for a class of finitely presented groups", Journal of Group Theory 17 (2014), no. 2, 361–378, https://doi.org/10.1515/jgt-2013-0050; read in arXiv:1109.2225v2 (Theorems 1.1 and 1.2, Propositions 3.2 and 3.3 and Lemma 6.1 of arXiv:1109.2225v2).
