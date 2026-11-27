# Two-locus ancestral process for n sequences

Fix two loci $A$ and $B$, a sample of $n \ge 2$ sequences and $\rho \ge 0$, with time scaled so that every pair of lineages coalesces at rate $1$ and every lineage ancestral at both loci recombines at rate $\rho/2$. While neither locus has reached its most recent common ancestor, the state is $(a, b, c)$: the numbers of lineages ancestral at $A$ only, at $B$ only, and at both loci, so that $a + c \ge 2$ and $b + c \ge 2$. The process starts at $(0, 0, n)$ and has the transitions

- $(a, b, c) \to (a, b, c-1)$ at rate $\binom c2$, and $(a-1, b, c)$, $(a, b-1, c)$ at rates $\binom a2 + ac$ and $\binom b2 + bc$ (a coalescence in which the merged lineage keeps the same type);
- $(a, b, c) \to (a-1, b-1, c+1)$ at rate $ab$ (an $A$-only and a $B$-only lineage coalesce into a lineage ancestral at both loci);
- $(a, b, c) \to (a+1, b+1, c-1)$ at rate $c\rho/2$ (recombination splits a lineage ancestral at both loci).

When a transition leaves a single lineage ancestral at $A$ ($a + c = 1$), locus $A$ has reached its most recent common ancestor: its material is removed, and the process continues as Kingman's coalescent of the $b + c$ lineages at $B$, all pairs coalescing at rate $1$; symmetrically for $B$. A transition that resolves both loci at once ends the process. $T_A$ and $T_B$ are the times at which $A$ and $B$ reach their most recent common ancestors.

This chain is the lumping, at two loci, of the [ancestral-material state space of the coalescent with recombination](coalescent-with-recombination-ancestral-material.md) under its reduced convention, in which lineages carrying no unresolved material are deleted. For $n = 2$ its states are the [six two-locus states](two-locus-state.md) and its rates are those of the [two-locus rate matrix](two-locus-rate.md): $(0,0,2)$ is linked, $(1,1,1)$ partly split and $(2,2,0)$ split.

## Depends on

- [Coalescent with recombination: ancestral-material state space and generator](coalescent-with-recombination-ancestral-material.md)
- [States of the two-locus ancestral process](two-locus-state.md)
- [Rate matrix of the two-locus coalescent](two-locus-rate.md)

## Expansion

A full proof page must still establish:

- that the transitions above are the image of the ancestral-material generator at two loci under the lumping map, including the removal of a resolved locus;
- that for $n = 2$ the chain has exactly the rate matrix $Q_\rho$ of the two-locus coalescent;
- the first-step equations for $\mathbb E[T_A T_B]$ for general $n$.

## Sources

- N. L. Kaplan and R. R. Hudson, "The use of sample genealogies for studying a selectively neutral m-loci model with recombination", *Theoretical Population Biology* 28(3):382–396, 1985
- R. C. Griffiths, "The two-locus ancestral graph", in *Selected Proceedings of the Sheffield Symposium on Applied Probability*, IMS Lecture Notes–Monograph Series 18, 1991, 100–117
