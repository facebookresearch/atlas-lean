# The universal theory of finite solvable groups of class 3 is undecidable

The universal theory of the finite groups in a certain variety of solvable groups of class 3 and the universal theory of all periodic groups are recursively inseparable; hence any set of finite groups containing all finite solvable groups of class 3 has undecidable universal theory.

A universal sentence in the first-order language of groups is a sentence $\forall x_1 \dots \forall x_k\, \Phi$ with $\Phi$ quantifier-free; the universal theory $\mathrm{Th}_\forall(\mathcal{C})$ of a class $\mathcal{C}$ of groups is the set of universal sentences true in every group of $\mathcal{C}$, and it is decidable if some algorithm decides membership in it. Two sets of sentences are recursively inseparable if no recursive set contains one and is disjoint from the complement of the other. Let $\mathcal{A}_p^2\mathcal{A} \cap \mathcal{Z}\mathcal{N}_5\mathcal{A}$ be the variety so denoted in the source, written with products of varieties ($\mathcal{A}_p$ abelian groups of exponent $p$, $\mathcal{A}$ abelian groups, $\mathcal{N}_5$ nilpotent groups of class at most $5$); its groups are solvable of derived length at most $3$. Then (Theorem 6.1 of the source):

1. the universal theories of the class of finite groups in $\mathcal{A}_p^2\mathcal{A} \cap \mathcal{Z}\mathcal{N}_5\mathcal{A}$ and of the class of all periodic groups are recursively inseparable;
2. in particular, the universal theory of any set of finite groups containing all finite solvable groups of class 3 is undecidable.

For the class of all finite groups the undecidability was proved by Slobodskoi.

## Depends on

- [Group](../../group-basics/group.md)
- [Abelian group](../../group-basics/abelian-group.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof follows Slobodskoi's idea, which goes back to Gurevich's proof for semigroups: there is a Turing machine for which the inputs it accepts and the inputs from which it runs forever through a cycle are recursively inseparable. The source simulates such machines by groups $G'(M_n)$ in the variety, so that a universal sentence fails in some finite group of the variety exactly in the cycling case and holds in all periodic groups in the accepting case.

## Sources

- O. Kharlampovich, A. Myasnikov and M. Sapir, "Algorithmically complex residually finite groups", Bulletin of Mathematical Sciences 7 (2017), no. 2, 309–352, https://doi.org/10.1007/s13373-017-0103-z; read in arXiv:1204.6506v5 (Theorem 6.1 of arXiv:1204.6506v5, with the variety notation of Section 6).
