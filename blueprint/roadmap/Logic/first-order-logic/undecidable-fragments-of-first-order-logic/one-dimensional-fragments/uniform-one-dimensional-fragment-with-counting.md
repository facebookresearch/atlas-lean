# Satisfiability of the uniform one-dimensional fragment with counting is undecidable

Adding counting quantifiers to the uniform one-dimensional fragment of first-order logic with equality makes satisfiability $\Pi^0_1$-complete and finite satisfiability $\Sigma^0_1$-complete, although the fragment without counting is NEXPTIME-complete.

**Setting (Kieroński and Kuusisto).** The *uniform one-dimensional fragment* $\mathrm{UF}_1^{=}$ over a relational vocabulary $\tau$ is the smallest set of formulas containing the unary $\tau$-atoms (atoms with one free variable), the identity atoms $x = y$, $\top$ and $\bot$, closed under $\neg$ and $\wedge$, and under the following quantification rule: for variables $X = \{x_0, \dots, x_k\}$, a finite set $U$ of fragment formulas with free variables in $X$, a set $V \subseteq X$ and a finite set $F$ of $\tau$-atoms whose variables are exactly $V$ (a *$V$-uniform* set), and a Boolean combination $\varphi$ of formulas in $U \cup F$, both $\exists x_1 \cdots \exists x_k\, \varphi$ and $\exists x_0 \cdots \exists x_k\, \varphi$ are in the fragment. Thus every quantifier block leaves at most one variable free (one-dimensionality), and all atoms with two or more variables in a block use the same variables (uniformity). The extension $\mathrm{UFC}_1^{=}$ also allows the counting quantifiers $\exists^{\geq k}$, $\exists^{\leq k}$ and $\exists^{= k}$ in place of $\exists$. The satisfiability problem asks whether a given sentence has a model, and finite satisfiability whether it has a finite model.

**Theorem (Kieroński and Kuusisto).**

1. The satisfiability problem of $\mathrm{UFC}_1^{=}$ is $\Pi^0_1$-complete (Theorem 5.2 of arXiv:1409.0731v1).
2. The finite satisfiability problem of $\mathrm{UFC}_1^{=}$ is $\Sigma^0_1$-complete (Theorem 5.3 of arXiv:1409.0731v1).

In contrast, satisfiability and finite satisfiability of $\mathrm{UF}_1^{=}$ itself are NEXPTIME-complete (Section 3 of the source), as is two-variable logic with counting quantifiers $\mathrm{FOC}^2$, as the source recalls. Dropping uniformity instead, the general one-dimensional fragment already has undecidable satisfiability (Hella and Kuusisto).

## Depends on

- [Complete theory of a first-order structure](../../theory-of-structure.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [The arithmetical class $\Sigma_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [The arithmetical class $\Pi_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)

## Proof depends on

- [The tiling problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

Membership in $\Pi^0_1$ and $\Sigma^0_1$ holds because $\mathrm{UFC}_1^{=}$ is a fragment of first-order logic, whose unsatisfiable sentences are recursively enumerable and whose finitely satisfiable sentences can be enumerated. Hardness comes from tiling: a $\mathrm{UFC}_1^{=}$ sentence $\eta$ over a ternary relation $R$ and a unary relation $E$ (marking even rows) axiomatizes grid-like structures, where $R(a, b, c)$ holds when $b$ is the horizontal successor of $a$ and $c$ the vertical successor of $b$, or with the roles exchanged on odd rows; counting quantifiers force each element to have exactly the right number of $R$-neighbours. Every grid-like model contains a homomorphic image of the infinite grid $\mathbb{N} \times \mathbb{N}$, so a tile set tiles the grid exactly when $\eta$ together with the tiling conditions is satisfiable, and periodic tilings correspond to finite models. The tiling problem is $\Pi^0_1$-complete and the periodic tiling problem $\Sigma^0_1$-complete. The tiling problem for the quarter plane is equivalent to that for the whole plane by a compactness argument. A complete expansion links a page for the $\Sigma^0_1$-completeness of the periodic tiling problem, which has none on main.

## Sources

- E. Kieroński and A. Kuusisto, "Complexity and Expressivity of Uniform One-Dimensional Fragment with Equality", in *Mathematical Foundations of Computer Science 2014 (MFCS 2014), Part I*, Lecture Notes in Computer Science 8634, Springer, 2014, pp. 365–376, doi:[10.1007/978-3-662-44522-8_31](https://doi.org/10.1007/978-3-662-44522-8_31); read as arXiv:1409.0731v1 ([arXiv](https://arxiv.org/abs/1409.0731v1)), whose numbering is used (counters within section): the definition of the fragment in Section 2, the complexity results of Section 3, and Theorems 5.2 and 5.3 of Section 5.
