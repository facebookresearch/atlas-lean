# Validity of two-variable dependence logic is undecidable

Although satisfiability of two-variable dependence logic is decidable, its validity problem is Σ⁰₁-hard, hence undecidable, because dependence logic is not closed under negation.

**Theorem (Kontinen, Kuusisto and Virtema).** Formulas of first-order logic in negation normal form over a relational vocabulary are evaluated in *team semantics*: a team $X$ is a set of assignments into a model $\mathfrak A$; literals hold in $X$ if they hold under every $s \in X$; $\psi \wedge \varphi$ holds if both hold; $\psi \vee \varphi$ holds if $X = Y \cup Z$ with $\mathfrak A \models_Y \psi$ and $\mathfrak A \models_Z \varphi$; $\exists x\,\psi$ holds if $\psi$ holds in $X[F/x]$ for some $F : X \to \mathcal P(A) \setminus \{\emptyset\}$; and $\forall x\,\psi$ holds if $\psi$ holds in $X[A/x]$. *Dependence logic* adds atoms $=\!(x_1, \ldots, x_n, y)$, true in $X$ iff any two assignments in $X$ agreeing on $x_1, \ldots, x_n$ agree on $y$. A sentence is true in $\mathfrak A$ if it holds in the team $\{\emptyset\}$, and *valid* if it is true in every model. Let $\mathcal D^2$ be the fragment of dependence logic with only the variables $x$ and $y$. The validity problem for $\mathcal D^2$ is undecidable, more precisely $\Sigma^0_1$-hard (Theorem 18 of the source).

The satisfiability and finite satisfiability problems of $\mathcal D^2$ are NEXPTIME-complete, as are those of the two-variable fragments of inclusion, exclusion, inclusion/exclusion and independence logic (Theorem 9). The source also shows that satisfiability of the prefix class $\exists^3\forall$ with a single generalized inclusion-type atom is undecidable, by translating the Kahr class $\forall\exists\forall$ (Theorem 22).

## Depends on

- [Two-variable logic and its counting extension](two-variable-logic-and-its-counting-extension.md)
- [The arithmetical class $\Sigma_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces the non-tiling problem, the complement of the tiling problem for the quadrant, which is $\Sigma^0_1$-complete (Corollary 11). For a tile set $T$ there is a two-variable first-order sentence $\varphi_T$, over $H$, $V$ and unary tile predicates, such that an $\{H, V\}$-structure is not $T$-tilable iff every expansion of it satisfies $\varphi_T$ (Lemma 12), and the grid is not $T$-tilable iff no *striped gridlike* structure is $T$-tilable (Lemma 15). Dependence atoms, used in two-variable formulas, characterize the striped gridlike structures among all models of a fixed vocabulary: a structure is striped and gridlike iff it does not satisfy a $\mathcal D^2$ sentence $\varphi_{\mathrm{non\text{-}grid}}$ (Lemma 17). Then $\varphi_{\mathrm{non\text{-}grid}} \vee \varphi_T$ is valid iff the grid is not $T$-tilable. The $\Sigma^0_1$-hardness rests on Theorem 10 of the source, that tiling of $\mathbb N \times \mathbb N$ is $\Pi^0_1$-complete, whose complement gives Corollary 11. A good expansion links a page for the $\Pi^0_1$-completeness of tiling the quadrant, and pages for the gridlike-structure characterization of Lemmas 12, 15 and 17.

## Sources

- J. Kontinen, A. Kuusisto and J. Virtema, "Decidability of Predicate Logics with Team Semantics", in *41st International Symposium on Mathematical Foundations of Computer Science (MFCS 2016)*, Leibniz International Proceedings in Informatics 58, Schloss Dagstuhl, 2016, paper 60, <https://doi.org/10.4230/LIPIcs.MFCS.2016.60>; numbers from arXiv:1410.5037v2, <https://arxiv.org/abs/1410.5037v2>: Definition 1 (lax team semantics), Section 2 (dependence atoms), Theorem 9, Sections 4 and 5 (Theorem 10, Corollary 11 and Lemmas 12 and 15 in Section 4; Lemma 17 and Theorem 18 in Section 5) and Theorem 22.
