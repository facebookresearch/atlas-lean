# Horn fragments of the Halpern–Shoham logic

The Halpern–Shoham logic HS has a diamond $\langle R\rangle$ and a box $[R]$ for each of Allen's interval relations, interpreted over the intervals of a linear order. Its Horn fragment allows only conjunctions of literals and of universal clauses $[U]\,(\lambda_1 \wedge \dots \wedge \lambda_k \to \lambda)$, with diamond-only and box-only subfragments.

**Intervals and relations.** For a linear order $\mathfrak{T} = (T, \leq)$, the intervals are the pairs $\langle x, y\rangle$ with $x \leq y$. Allen's relations between $\langle x_1, y_1\rangle$ and $\langle x_2, y_2\rangle$ are, as displayed in Section 2 of the source: After ($y_1 = x_2$ and $x_2 < y_2$), Begins ($x_1 = x_2$, $y_2 < y_1$), Ends ($x_1 < x_2$, $y_1 = y_2$), During ($x_1 < x_2$, $y_2 < y_1$), Later ($y_1 < x_2$), Overlaps ($x_1 < x_2 < y_1 < y_2$), and $\bar A$ ($y_2 = x_1$ and $x_2 < y_2$), $\bar B$ ($x_1 = x_2$, $y_1 < y_2$), $\bar E$ ($x_2 < x_1$, $y_1 = y_2$), $\bar D$ ($x_2 < x_1$, $y_1 < y_2$), $\bar L$ ($y_2 < x_1$) and $\bar O$ ($x_2 < x_1 < y_2 < y_1$). Five of these are the converses of the corresponding relations; $\bar A$ is not quite the converse of After, since it requires $x_2 < y_2$ rather than $x_1 < y_1$ (for $\langle 1,1\rangle \bar A \langle 0,1\rangle$, the converse would need $\langle 0, 1\rangle$ After $\langle 1,1\rangle$, which fails). This is the *irreflexive* semantics; the *reflexive* semantics replaces each $<$ by $\leq$, and results stated for *arbitrary* semantics are true whichever choice is made for each relation.

**Horn formulas.** Literals are $\lambda ::= \top \mid \bot \mid p \mid \langle R\rangle\lambda \mid [R]\lambda$ for interval relations $R$. Formulas of the Horn fragment $\mathcal{HS}_{\mathit{horn}}$ are

$$
\varphi ::= \lambda \mid [U]\,(\lambda_1 \wedge \dots \wedge \lambda_k \to \lambda) \mid \varphi_1 \wedge \varphi_2,
$$

where $[U]$ is the universal modality: $[U]\psi$ is true iff $\psi$ is true at every interval. $\mathcal{HS}^\Diamond_{\mathit{horn}}$ consists of the Horn formulas without box operators $[R]$, $\mathcal{HS}^\Box_{\mathit{horn}}$ of those without diamonds $\langle R\rangle$, and the core fragments allow only clauses $[U]\,(\lambda_1 \to \lambda_2)$ and $[U]\,(\lambda_1 \wedge \lambda_2 \to \bot)$.

**Satisfiability.** A model on $\mathfrak{T}$ assigns sets of intervals to propositional variables. For a class $\mathcal{C}$ of linear orders, a formula is $\mathcal{C}$-satisfiable (respectively $\mathcal{C}(<)$- or $\mathcal{C}(\leq)$-satisfiable) if it is true at some interval of some model based on an order in $\mathcal{C}$, under the arbitrary (irreflexive, reflexive) semantics. A linear order is *discrete* if every non-maximal point has an immediate successor and every non-minimal point an immediate predecessor; $\mathrm{Fin}$ is the class of finite linear orders.

## Depends on

- [Partially ordered set](../../../Order/ordered-sets/partial-order.md)

## Proof depends on

None.

## Expansion

Every HS formula is equisatisfiable with a formula in clausal normal form, conjunctions of literals, negated literals and universal clauses $[U]\,(\neg\lambda_1 \vee \dots \vee \neg\lambda_n \vee \lambda_{n+1} \vee \dots \vee \lambda_{n+m})$; the Horn fragment keeps at most one positive literal per clause, by analogy with Datalog. Full HS is highly undecidable (Halpern and Shoham), and the box-only Horn fragment is tractable over all orders under the reflexive semantics and over dense orders under the irreflexive semantics.

## Sources

- D. Bresolin, A. Kurucz, E. Muñoz-Velasco, V. Ryzhikov, G. Sciavicco and M. Zakharyaschev, "Horn fragments of the Halpern–Shoham interval temporal logic", *ACM Transactions on Computational Logic* 18(3), Article 22, 2017, 39 pp., doi:10.1145/3105909; read as arXiv:1604.03515v5, <https://arxiv.org/abs/1604.03515v5>: Section 1 (clausal normal form and the Horn fragments) and Section 2 (intervals, Allen's relations, the reflexive and irreflexive semantics, models and satisfiability).
