# Word and conjugacy problems of finitely presented groups realize every pair of comparable c.e. degrees

For any computably enumerable Turing degrees $W \le_T C$ there is a finitely presented group whose word problem has degree $W$ and whose conjugacy problem has degree $C$. In particular some finitely presented group has solvable word problem and unsolvable conjugacy problem.

For a set $A \subseteq \mathbb{N}$, its *Turing degree* is its equivalence class under mutual Turing reducibility; a degree is *c.e.* if it contains a computably enumerable set. For a finitely presented group $G$, the word problem and the conjugacy problem are sets of words and pairs of words, and their degrees are defined through a computable coding of words by natural numbers.

**Theorem (Collins).** Given c.e. degrees $W$ and $C$ with $W \le_T C$, there is a finitely presented group $G$ whose word problem has degree $W$ and whose conjugacy problem has degree $C$.

Conventions: the word problem of any finitely presented group is Turing reducible to its conjugacy problem, since it is the special case with second word empty, and both are computably enumerable. The theorem says that this is the only relation between their degrees.

## Depends on

- [Solvable word problem](word-problem-solvable.md)
- [Solvable conjugacy problem for a quotient of a free group](../decision-problems-in-free-abelianized-extensions/conjugacy-problem-solvable.md)
- [Group](../../group-basics/group.md)
- [Turing degree of a predicate](../../../TheoryOfComputation/degrees-and-hierarchies/turing-degrees-and-the-turing-jump/turing-degree-of.md)
- [Turing reducibility of predicates](../../../TheoryOfComputation/degrees-and-hierarchies/turing-degrees-and-the-turing-jump/turing-reducible-pred.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

None.

## Expansion

Collins's proof starts from computably enumerable sets of the given degrees and builds a finitely presented group from them with the embedding techniques of combinatorial group theory (free products with amalgamation, HNN extensions and embeddings of recursively presented groups into finitely presented ones), controlling the degrees of the word and conjugacy problems along the way. The case $W = 0$, $C = 0'$ gives a finitely presented group with solvable word problem and unsolvable conjugacy problem.

## Sources

- Bjorn Poonen, *Undecidable problems: a sampler*, in: Interpreting Gödel: Critical Essays (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, https://doi.org/10.1017/CBO9780511756306.015, read in the copy arXiv:1204.0299v2, where the statement is Theorem 6.1, with the explanation of degrees and reducibility after it.
- Donald J. Collins, *Representation of Turing reducibility by word and conjugacy problems in finitely presented groups*, Acta Math. 128 (1972), 73–90, https://doi.org/10.1007/BF02392160, the original source, cited beside the survey read above.
