# Some Cayley automatic group has undecidable conjugacy problem

There are Cayley automatic groups with undecidable conjugacy problem; consequently Cayley automatic groups need not be Cayley biautomatic.

A finitely generated group $G$ with finite generating set $S$ is Cayley automatic (Kharlampovich, Khoussainov and Miasnikov) if there are a finite alphabet $\Sigma$, a regular language $L \subseteq \Sigma^*$ and a bijection $\psi\colon L \to G$ such that for each $s \in S$ the relation $\{(u, v) \in L^2 : \psi(v) = \psi(u) s\}$ is recognized by a synchronous two-tape finite automaton; unlike for automatic groups, the words of $L$ need not be words in the generators. There are Cayley automatic groups with undecidable conjugacy problem (Theorem 2 of the source).

Since Cayley biautomatic groups have decidable conjugacy problem, there are Cayley automatic groups that are not Cayley biautomatic. The source also shows that the isomorphism problem is undecidable in the class of Cayley automatic groups (Theorem 3).

## Depends on

- [Group](../../../group-basics/group.md)
- [Solvable conjugacy problem for a quotient of a free group](../../decision-problems-in-free-abelianized-extensions/conjugacy-problem-solvable.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Some free-abelian-by-free groups with fibre of rank four have unsolvable conjugacy problem](../conjugacy-problem-in-group-extensions/free-abelian-by-free-unsolvable-conjugacy.md)

## Expansion

All groups $\mathbb{Z}^d \rtimes F_n$ are Cayley automatic (a consequence of results of Kharlampovich, Khoussainov and Miasnikov). Bogopolski, Martino and Ventura gave groups of this form with undecidable conjugacy problem, which gives the theorem; Levitt's undecidability of the isomorphism problem in the class of groups $\mathbb{Z}^d \rtimes F_n$ gives the companion result on isomorphism. The examples are not automatic in the usual sense: a group $\mathbb{Z}^d \rtimes F_n$ with subexponential Dehn function has decidable conjugacy problem.

## Sources

- A. Miasnikov and Z. Šunić, "Cayley graph automatic groups are not necessarily Cayley graph biautomatic", Language and Automata Theory and Applications (LATA 2012), Lecture Notes in Computer Science 7183 (2012), 401–407, https://doi.org/10.1007/978-3-642-28332-1_34; read in arXiv:1108.2759v1 (titled "Cayley automatic groups are not Cayley biautomatic") (Theorems 2 and 3, with the results of Kharlampovich–Khoussainov–Miasnikov, Bogopolski–Martino–Ventura and Levitt quoted in the introduction, of arXiv:1108.2759v1).
