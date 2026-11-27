# Provability in the logic of bunched implications is undecidable

Provability in the logic of bunched implications BI is undecidable; equivalently, the equational theory of BI-algebras is undecidable. More generally, every class of distributive residuated lattices with a disjointive negation that contains one specific powerset algebra has an undecidable equational theory.

**Setting.** Formulas of [BI](../logic-of-bunched-implications.md) are built from propositional letters and $\top, \bot, 1$ with $\wedge$, $\vee$, $\to$ and the multiplicatives $\ast$, $\mathrel{-\!\!\ast}$; bunches are built from formulas and the units $\varnothing_+$, $\varnothing_\times$ with the additive and multiplicative combinations $;$ and $,$, and provability refers to the bunched sequent calculus LBI. A *BI-algebra* $(A, \wedge, \vee, \to, \top, \bot, \ast, \mathrel{-\!\!\ast}, 1)$ is a Heyting algebra with a commutative monoid $(A, \ast, 1)$ residuated by $\mathrel{-\!\!\ast}$: $x \ast y \leq z$ iff $y \leq x \mathrel{-\!\!\ast} z$. A *disjointive distributive residuated lattice* $(A, \wedge, \vee, \top, \bot, \neg, \cdot, \backslash, /)$ is a bounded distributive lattice with a semigroup $(A, \cdot)$ residuated by $\backslash$ and $/$, and a unary operation with $x \wedge \neg x = \bot$. The algebra $\mathcal{P}_\omega(\mathbb{N})^+$ has universe the set of all sets of finite subsets of $\mathbb{N}$, Boolean operations, $X \ast Y = \{x \cup y : x \in X, y \in Y\}$, its residual, and unit $\{\varnothing\}$.

**Theorem (Galatos, Jipsen, Knudstorp and Ramanayake).**

1. Every class of disjointive distributive residuated lattices that contains $\mathcal{P}_\omega(\mathbb{N})^+$ has an undecidable equational theory.
2. Consequently, provability in BI is undecidable: there is no algorithm deciding, for a formula $\varphi$, whether the sequent $\top \Rightarrow \varphi$ is derivable in LBI. This holds already for formulas in the language $\{\wedge, \vee, \neg, \mathrel{-\!\!\ast}\}$, with $\neg\alpha = \alpha \to \bot$.
3. The equational theories of the non-commutative variant GBI, of Boolean BI (BBI), and of the variety of disjointive distributive residuated lattices are undecidable.

By contrast, the variety of distributive residuated lattices with unit has a decidable equational theory (Kozak), so adding an operation with $x \wedge \neg x = \bot$ already crosses into undecidability.

## Depends on

- [Logic of bunched implications](../logic-of-bunched-implications.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

To each finite set $\mathcal{W}$ of Wang tiles one computably associates a formula $\varphi_{\mathcal{W}}$ in the language $\{\wedge, \vee, \neg, \backslash, /\}$. If some disjointive distributive residuated lattice refutes $\varphi_{\mathcal{W}}$ (that is, $\top \leq \varphi_{\mathcal{W}}$ fails), then $\mathcal{W}$ tiles $\mathbb{N}^2$; conversely, if $\mathcal{W}$ tiles $\mathbb{N}^2$, then $\mathcal{P}_\omega(\mathbb{N})^+$ refutes $\varphi_{\mathcal{W}}$, via its ternary relational presentation. Hence $\mathcal{W}$ tiles the quadrant iff the class refutes $\varphi_{\mathcal{W}}$, and the tiling problem reduces to the complement of the equational theory. Since $\mathcal{P}_\omega(\mathbb{N})^+$ is a BBI-algebra, hence a BI- and GBI-algebra, and BI-algebras are algebraic semantics for LBI, clauses 2 and 3 follow. The source also identifies gaps in earlier publications that claimed decidability of BI, and gives a second proof for GBI and BI via and-branching counter machines and residuated frames.

## Sources

- N. Galatos, P. Jipsen, S. B. Knudstorp and R. Ramanayake, "The logic of bunched implications is undecidable", in *41st Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2026)*, Leibniz International Proceedings in Informatics, Schloss Dagstuhl, 2026, article 46, doi:10.4230/LIPIcs.LICS.2026.46; read as arXiv:2603.01595v1, <https://arxiv.org/abs/2603.01595v1>: Section 2 (formulas, bunches, BI- and GBI-algebras, disjointive distributive residuated lattices, the algebra $\mathcal{P}_\omega(\mathbb{N})^+$, the main theorem and the theorems that BI, GBI, BBI and disjointive distributive residuated lattices are undecidable), Section 3 (the tiling proofs) and the final section of arXiv:2603.01595v1.
