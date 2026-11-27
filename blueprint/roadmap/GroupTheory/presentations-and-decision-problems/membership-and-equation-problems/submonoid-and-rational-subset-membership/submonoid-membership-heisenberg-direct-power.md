# Some direct power of the Heisenberg group has a submonoid with undecidable membership

For all sufficiently large $n$, the direct power $\mathbb{H}^n$ of the integer Heisenberg group contains a fixed finitely generated submonoid with undecidable membership problem; so do free nilpotent groups of class at least 2 and large rank.

Let $\mathbb{H}$ be the integer Heisenberg group, the group of upper unitriangular $3 \times 3$ integer matrices, equivalently the free nilpotent group of class $2$ and rank $2$, and let $\mathbb{H}^n$ be the direct product of $n$ copies of $\mathbb{H}$. For a finitely generated submonoid $M$ of a finitely generated group $G$, the membership problem for $M$ asks, given an element $g \in G$ as a word in the generators, whether $g \in M$ (see [submonoid membership problem](submonoid-membership-problem.md)).

**Theorem (Roman'kov).**

1. For every sufficiently large $n \in \mathbb{N}$, the group $\mathbb{H}^n$ contains a finitely generated submonoid $M$ whose membership problem is undecidable (Theorem 5.2 of arXiv:2209.14786v1).
2. If a $k$-generated nilpotent group of class $c$ contains a finitely generated submonoid with undecidable membership problem, then so does the free nilpotent group $N_{k,c}$ of rank $k$ and class $c$ (Proposition 5.3 of arXiv:2209.14786v1). Hence for every $c \geq 2$ and every sufficiently large $k$, $N_{k,c}$ contains a finitely generated submonoid with undecidable membership problem.

This answers a question of Lohrey and Steinberg whether some finitely generated nilpotent group has undecidable submonoid membership, and a question of Colcombet, Ouaknine, Semukhin and Worrell for direct powers of $\mathbb{H}$. The submonoid is fixed; only the element varies.

## Depends on

- [Submonoid membership problem](submonoid-membership-problem.md)
- [Group](../../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Take a Diophantine equation $D(x_1, \dots, x_m) = \upsilon$ with a fixed polynomial $D$ and a parameter $\upsilon$ whose solvability in integers is undecidable, which exists by the undecidability of Hilbert's tenth problem. It is rewritten as an equivalent system of equations of the forms $x + y = z$ and $xy = z$ in nonnegative integers (a Skolem system). Theorem 5.1 of the source builds, from $D$ alone, a power $\mathbb{H}^n$, a finitely generated submonoid $M$ and, for each $\upsilon$, an element $g(\upsilon)$ such that $g(\upsilon) \in M$ exactly when the system is solvable: each equation of the system gets a block of copies of $\mathbb{H}$; in a multiplication block, the commutator of powers $a^x$ and $b^y$ of the two generators of $\mathbb{H}$ is the power of the central generator with exponent $xy$, and the generators of $M$ tie together the exponents used in different copies. For part 2, the full preimage of $M$ under a surjection $N_{k,c} \to G$ is a finitely generated submonoid, since the kernel is a finitely generated subgroup of the Noetherian group $N_{k,c}$. A complete expansion links a page for the fact that every subgroup of a finitely generated nilpotent group is finitely generated, which has none.

## Sources

- V. A. Roman'kov, "Undecidability of the submonoid membership problem for free nilpotent group of class $l \geq 2$ of sufficiently large rank", *Izvestiya: Mathematics* 87(4):798–816, 2023, doi:10.4213/im9342e; read as arXiv:2209.14786v1, <https://arxiv.org/abs/2209.14786v1>: Theorems 5.1 and 5.2 and Proposition 5.3, with the numbering of that version.
