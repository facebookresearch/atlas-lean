# A finitely generated, recursively presented orbit undecidable subgroup of Aut(F3)

There is a finitely generated subgroup $A$ of $\mathrm{Aut}(F_3)$, not finitely presented but with an explicit one-parameter recursive presentation, such that no algorithm decides, for $u, v \in F_3$, whether some element of $A$ maps $u$ to a conjugate of $v$.

For a group $F$, a subgroup $A \le \mathrm{Aut}(F)$ is orbit decidable if some algorithm decides, given $u, v \in F$, whether $v$ is conjugate to $\alpha(u)$ for some $\alpha \in A$, and orbit undecidable otherwise. There exists a finitely generated, not finitely presented, orbit undecidable subgroup $A \le \mathrm{Aut}(F_3)$ admitting a one-parameter recursive presentation (Theorem 4.2 of the source).

The source's main theorem gives an explicit recursive presentation of Mihailova's subgroup $M(H) \le F_n \times F_n$ for every finite, concise and Peiffer aspherical presentation of $H$ (Theorem 1.1), partially answering a question of Grigorchuk.

## Depends on

- [Group](../../../group-basics/group.md)
- [Recursively presented group](../../../orderable-groups/word-problem-for-orderable-groups/is-recursively-presented.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Embed $F_2 \times F_2$ in $\mathrm{Aut}(F_3)$, with $F_3 = \langle q, a, b \rangle$, as the subgroup $B$ of automorphisms $q \mapsto uqv$, $a \mapsto a$, $b \mapsto b$ for $u, v \in \langle a, b \rangle$. By a result of Bogopolski, Martino and Ventura (Lemma 4.1 of the source, quoting Proposition 7.3 of their paper), every subgroup $A \le B$ whose membership problem in $B$ is undecidable is orbit undecidable in $\mathrm{Aut}(F_3)$. Collins and Miller constructed a finite, concise and Peiffer aspherical presentation of a group $H$ with unsolvable word problem; by Mihailova's construction, the subgroup $M(H) \le F_n \times F_n$ is finitely generated and has unsolvable membership problem, and $F_n \times F_n$ embeds in $B$ with finite index. So $A = M(H)$ is orbit undecidable, and Theorem 1.1 gives its explicit one-parameter recursive presentation; $A$ is not finitely presented. The Collins–Miller presentation, Mihailova's theorem and the Bogopolski–Martino–Ventura criterion have no pages here. That criterion also relates orbit decidability of the action subgroup of an extension $1 \to F \to G \to P \to 1$, under conditions on $F$ and $P$, to solvability of the conjugacy problem in $G$.

## Sources

- O. Bogopolski and E. Ventura, "A recursive presentation for Mihailova's subgroup", Groups, Geometry, and Dynamics 4 (2010), no. 3, 407–417, https://doi.org/10.4171/GGD/88; read in arXiv:0810.0690v1, whose numbering is used here (Theorems 1.1 and 4.2 and Lemma 4.1 of arXiv:0810.0690v1).
