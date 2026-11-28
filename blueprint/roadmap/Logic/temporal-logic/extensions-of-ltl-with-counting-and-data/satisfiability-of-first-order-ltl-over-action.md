# Satisfiability of first-order LTL over action traces is undecidable

The first-order extension of LTL used for runtime monitoring, in which quantifiers range over the arguments of actions observed at the current position, has an undecidable satisfiability problem.

**Theorem (Bauer, Küster and Vegliach).** Fix a sorted signature $\Gamma$ with finitely many sorts, constants and function symbols, *interpreted operators* $r$ (relations with a fixed computable interpretation) and *uninterpreted operators* $p$ (whose extensions are given by the trace). A first-order structure $\mathcal A$ interprets each sort by a nonempty finite or countable set and the constants, functions and interpreted operators by computable functions and relations; an *action* is a pair $(p, \mathbf d)$ of an uninterpreted operator and a tuple of domain values, and a trace $w = w_0 w_1 \cdots$ is a finite or infinite sequence of finite sets of actions. Formulas of $\mathrm{LTL}^{\mathrm{FO}}$ are

$$
\varphi ::= p(t_1, \ldots, t_n) \mid r(t_1, \ldots, t_n) \mid \neg\varphi \mid \varphi \wedge \varphi \mid \mathsf X\varphi \mid \varphi\,\mathsf U\,\varphi \mid \forall(x_1, \ldots, x_n) : p.\,\varphi,
$$

where $p(t_1, \ldots, t_n)$ holds at position $i$ if $(p, \mathbf d) \in w_i$ for the values $\mathbf d$ of the terms, $\mathsf X$ and $\mathsf U$ are as in LTL on $w$, and $\forall(x_1, \ldots, x_n) : p.\,\varphi$ holds at $i$ if $\varphi$ holds for every action $(p, d_1, \ldots, d_n) \in w_i$ with $x_j$ bound to $d_j$. A sentence $\psi$ is satisfiable if $(\mathcal A, w) \models \psi$, at position $0$, for some structure $\mathcal A$ and nonempty trace $w$. Satisfiability of $\mathrm{LTL}^{\mathrm{FO}}$ is undecidable (Theorem 2 of the source).

The source nevertheless gives a sound monitoring procedure for $\mathrm{LTL}^{\mathrm{FO}}$ based on spawning automata, and shows that the prefix problem for $\mathrm{LTL}^{\mathrm{FO}}$, whether every extension of a given finite trace satisfies (or violates) a sentence, is undecidable as well (Theorem 5).

## Depends on

- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

For each first-order sentence $\varphi$ one constructs an $\mathrm{LTL}^{\mathrm{FO}}$ sentence $\psi$ that is satisfiable iff $\varphi$ has a finite model (Lemma 1, proved in the appendix of the source): a fresh uninterpreted operator $d$ marks the finite domain, quantifiers are relativized to it, and a trace with a single event, listing the tuples of each predicate and the elements of $d$, witnesses a finite model. Finite satisfiability of first-order logic is undecidable by Trakhtenbrot's theorem, which gives the result.

## Sources

- A. Bauer, J.-C. Küster and G. Vegliach, "From Propositional to First-Order Monitoring", in *Runtime Verification (RV 2013)*, Lecture Notes in Computer Science 8174, Springer, 2013, pp. 59–75, <https://doi.org/10.1007/978-3-642-40787-1_4>; numbers from arXiv:1303.3645v1, <https://arxiv.org/abs/1303.3645v1>: Section 4 (syntax and semantics of $\mathrm{LTL}^{\mathrm{FO}}$, Lemma 1, Theorems 2 and 5) and the abstract.
