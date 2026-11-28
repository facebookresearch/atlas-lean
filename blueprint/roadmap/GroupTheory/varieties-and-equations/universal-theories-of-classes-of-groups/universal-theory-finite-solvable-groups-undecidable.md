# The universal theory of finite solvable groups of derived length at most 3 is undecidable

The universal theory of the finite groups in a certain variety of solvable groups of derived length at most 3 and the universal theory of all periodic groups are recursively inseparable; hence any set of finite groups containing all finite solvable groups of derived length at most 3 has undecidable universal theory.

A universal sentence in the first-order language of groups is a sentence $\forall x_1 \dots \forall x_k\, \Phi$ with $\Phi$ quantifier-free; the universal theory $\mathrm{Th}_\forall(\mathcal{C})$ of a class $\mathcal{C}$ of groups is the set of universal sentences true in every group of $\mathcal{C}$, and it is decidable if some algorithm decides membership in it. Two sets of sentences are recursively inseparable if no recursive set contains one and is disjoint from the complement of the other. Fix a prime $p$ (the source fixes one, say $p = 2$). Let $\mathcal{A}_p^2\mathcal{A} \cap \mathcal{Z}\mathcal{N}_5\mathcal{A}$ be the variety so denoted in the source, written with products of varieties, where $\mathcal{U}\mathcal{V}$ is the variety of extensions of groups in $\mathcal{U}$ by groups in $\mathcal{V}$ and $\mathcal{Z}\mathcal{V}$ is the variety of all central extensions of groups in $\mathcal{V}$ ($\mathcal{A}_p$ abelian groups of exponent $p$, $\mathcal{A}$ abelian groups, $\mathcal{N}_5$ nilpotent groups of class at most $5$); its groups are solvable of derived length at most $3$. Then (Theorem 6.1 of the source):

1. the universal theories of the class of finite groups in $\mathcal{A}_p^2\mathcal{A} \cap \mathcal{Z}\mathcal{N}_5\mathcal{A}$ and of the class of all periodic groups are recursively inseparable;
2. in particular, the universal theory of any set of finite groups containing all finite solvable groups of derived length at most 3 ("solvable of class 3" in the source) is undecidable.

For the class of all finite groups the undecidability was proved by Slobodskoi. Derived length cannot be replaced by nilpotency class here: by Remark 6.2 of the source, the universal theory of the finite groups of a finitely based variety in which every finitely generated group is residually finite is decidable, and the variety of nilpotent groups of class at most $3$ is such a variety, since finitely generated nilpotent groups are residually finite.

## Depends on

- [Group](../../group-basics/group.md)
- [Abelian group](../../group-basics/abelian-group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Varieties of groups](../axiomatizable-classes-of-groups/is-variety.md)
- [The first-order language of groups](../../../Logic/model-theory/first-order-language-of-groups/group-language.md)
- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof follows Slobodskoi's idea, which goes back to Gurevich's proof for semigroups: there is a Turing machine for which the set of inputs it accepts and the set of inputs on which it never stops are recursively inseparable. The source simulates such a machine, through a Minsky machine $M_n$, by a finitely presented group $G'(M_n)$ in the variety with defining relations $R$, and assigns to each input $\epsilon$ a word $w(\epsilon)$. If the machine accepts $\epsilon$, some finite image of $G'(M_n)$, a finite group of the variety, falsifies the universal sentence $\&R \to w(\epsilon) = 1$; if the machine never stops on $\epsilon$, the sentence holds in every periodic image of $G'(M_n)$, hence in every periodic group. Recursive inseparability of the two sets of inputs transfers to the two sets of sentences.

## Sources

- O. Kharlampovich, A. Myasnikov and M. Sapir, "Algorithmically complex residually finite groups", Bulletin of Mathematical Sciences 7 (2017), no. 2, 309–352, https://doi.org/10.1007/s13373-017-0103-z; read in arXiv:1204.6506v5 (Theorem 6.1 and Remark 6.2 of arXiv:1204.6506v5, with the variety notation of Section 4 and the prime fixed in Section 4.1).
