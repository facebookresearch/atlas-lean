# Nilpotent and 0-simple semigroups, divisibility and eventual embeddings

These are basic notions for embedding problems of finite semigroups: nilpotent semigroups, whose long products vanish, 0-simple semigroups, which have no proper nonzero ideals, divisibility of elements, and properties that hold in some larger semigroup.

Let $S$ be a semigroup, and let $S^1$ be $S$ with an identity adjoined if it has none. An element $0$ is a *zero* if $0x = x0 = 0$ for all $x$. A semigroup with zero is *$k$-nilpotent* if every product of $k$ elements equals $0$. A semigroup $S$ with zero is *0-simple* if $S^2 \ne \{0\}$ and its only ideals are $\{0\}$ and $S$.

An element $b$ *divides* $a$ in $S$ if $a = x b y$ for some $x, y \in S^1$; Green's relations $\mathcal L$, $\mathcal R$, $\mathcal H$ and $\mathcal J$ are as in [Green's relations](../../../TheoryOfComputation/regular-languages/syntactic-monoids/varieties-and-algebraic-characterizations/green-s-relations-and-j-trivial-monoids.md), so that $a \,\mathcal J\, b$ means that each of $a$, $b$ divides the other. For a semigroup $S$ contained in a larger semigroup $T$ (a *supersemigroup*), a property holds *eventually* if it holds in some supersemigroup $T$, either in the class of all semigroups or in the class of finite semigroups.

## Depends on

- [Semigroup presentations and the word problem](../decision-problems-in-semigroups/semigroup-presentations-and-the-word-problem.md)
- [Green's relations and J-trivial monoids](../../../TheoryOfComputation/regular-languages/syntactic-monoids/varieties-and-algebraic-characterizations/green-s-relations-and-j-trivial-monoids.md)

## Proof depends on

None.

## Expansion

Divisibility and the eventual versions of Green's relations are the subject of Rhodes' problem and its variants.

## Sources

- Mark Sapir, "Minsky Machines and Algorithmic Problems", in *Fields of Logic and Computation II*, Lecture Notes in Computer Science 9300, Springer, 2015, pp. 273–292, doi:[10.1007/978-3-319-23534-9_17](https://doi.org/10.1007/978-3-319-23534-9_17); read in arXiv:1504.07736v1 ([arXiv](https://arxiv.org/abs/1504.07736v1)), whose numbering is used: Section 6.2 (subsemigroups of finite 0-simple semigroups, 4-nilpotent semigroups, divisibility and Rhodes' problem).
- Marcel Jackson, "Some undecidable embedding problems for finite semigroups", *Proceedings of the Edinburgh Mathematical Society* 42(1), 1999, pp. 113–125, doi:[10.1017/S0013091500020058](https://doi.org/10.1017/S0013091500020058); read in the open-access publisher copy (Cambridge University Press): Section 1 (Green's relations and eventual embeddings).
