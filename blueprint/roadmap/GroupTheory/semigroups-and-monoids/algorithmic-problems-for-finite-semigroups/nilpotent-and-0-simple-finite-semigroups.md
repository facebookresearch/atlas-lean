# Nilpotent and 0-simple semigroups, divisibility and eventual embeddings

These are basic notions for embedding problems of finite semigroups: nilpotent semigroups, whose long products vanish, 0-simple semigroups, which have no proper nonzero ideals, divisibility of elements, and properties that hold in some larger semigroup.

Let $S$ be a semigroup, and let $S^1$ be $S$ with an identity adjoined if it has none. An element $0$ is a *zero* if $0x = x0 = 0$ for all $x$. A semigroup with zero is *$k$-nilpotent* if every product of $k$ elements equals $0$. A semigroup $S$ with zero is *0-simple* if $S^2 \ne \{0\}$ and its only ideals are $\{0\}$ and $S$. The survey states only the condition on ideals; the condition $S^2 \ne \{0\}$ excludes the two-element semigroup $\{0, a\}$ with $a^2 = 0$, which has no other ideals but is not of the Rees–Sushkevich form that Section 6.2.A gives for finite 0-simple semigroups.

An element $b$ *divides* $a$ in $S$ if $a = x b y$ for some $x, y \in S^1$; Green's relations $\mathcal L$, $\mathcal R$, $\mathcal H$ and $\mathcal J$ are as in [Green's relations](../../../TheoryOfComputation/regular-languages/syntactic-monoids/varieties-and-algebraic-characterizations/green-s-relations-and-j-trivial-monoids.md), so that $a \,\mathcal J\, b$ means that each of $a$, $b$ divides the other. For a finite semigroup $S$, a supersemigroup is a semigroup $T$ containing $S$ as a subsemigroup. For one of Green's relations $\mathcal U$ and a class $\mathcal K$ of semigroups (all semigroups, or the finite ones), a set $A \subseteq S \times S$ is *eventually $\mathcal U$-related in $\mathcal K$* if $A \subseteq \mathcal U^T$ for some supersemigroup $T \in \mathcal K$ of $S$, and a subset $A \subseteq S$ is *eventually $\mathcal U$-embeddable in $\mathcal K$* if $A \times A$ is eventually $\mathcal U$-related in $\mathcal K$ (Definition 2.1 of Jackson). Likewise, $b$ *eventually divides* $a$ if $a = x b y$ for some elements $x, y$ of a finite supersemigroup of $S$, that is, if the equation $a = x_1 b x_2$ is solvable over $S$ (survey, Section 6.2.B).

## Depends on

- [Semigroup presentations and the word problem](../decision-problems-in-semigroups/semigroup-presentations-and-the-word-problem.md)
- [Green's relations and J-trivial monoids](../../../TheoryOfComputation/regular-languages/syntactic-monoids/varieties-and-algebraic-characterizations/green-s-relations-and-j-trivial-monoids.md)

## Proof depends on

None.

## Expansion

Divisibility and the eventual versions of Green's relations are the subject of Rhodes' problem and its variants.

## Sources

- Mark Sapir, "Minsky Machines and Algorithmic Problems", in *Fields of Logic and Computation II*, Lecture Notes in Computer Science 9300, Springer, 2015, pp. 273–292, doi:[10.1007/978-3-319-23534-9_17](https://doi.org/10.1007/978-3-319-23534-9_17); read in arXiv:1504.07736v1 ([arXiv](https://arxiv.org/abs/1504.07736v1)), whose numbering is used: Section 6.2 (Section 6.2.A: 0-simple semigroups, their Rees–Sushkevich form and 4-nilpotent semigroups; Section 6.2.B: equations over finite semigroups, divisibility and Rhodes' problem).
- Marcel Jackson, "Some undecidable embedding problems for finite semigroups", *Proceedings of the Edinburgh Mathematical Society* 42(1), 1999, pp. 113–125, doi:[10.1017/S0013091500020058](https://doi.org/10.1017/S0013091500020058); read in the open-access publisher copy (Cambridge University Press): Section 1 (Green's relations) and Definition 2.1 in Section 2 (eventually related sets and eventual embeddings).
