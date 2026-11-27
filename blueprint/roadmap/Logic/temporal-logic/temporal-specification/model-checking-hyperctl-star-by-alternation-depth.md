# Complexity of HyperCTL* model checking

Let $g_c(0, y) = y$ and $g_c(x, y) = c^{g_c(x - 1, y)}$ be towers of exponentials, with $\mathrm{NSPACE}(g_c(-1, y))$ read as $\mathrm{NLOGSPACE}$, the class [NL](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/nl.md), and let
[nondeterministic space classes](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/nspace.md) be as usual.

**Theorem (Clarkson, Finkbeiner, Koleini, Micinski, Rabe and Sánchez).** The model checking problem for [HyperCTL*](hyperctl-star.md) specifications $\varphi$ of alternation depth $k$ on
finite, explicitly given Kripke structures $K$, measured in the size of the formula, is complete for $\mathrm{NSPACE}(g_c(k, |\varphi|))$; and for a fixed specification of alternation depth $k$,
measured in the size of the structure, it lies in $\mathrm{NSPACE}(g_c(k - 1, |K|))$, for some constant $c > 0$. In particular it is decidable.

Both bounds go through satisfiability of quantified propositional temporal logic in prenex form; the quantifier alternations of that logic are not the same
measure as the alternation depth of the translated HyperCTL* formula, which also counts $\mathbf U$ and $\mathbf R$.

## Depends on

- [HyperCTL*](hyperctl-star.md)
- [The complexity class NL](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/nl.md)
- [Nondeterministic space classes](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/nspace.md)

## Sources

- M. R. Clarkson, B. Finkbeiner, M. Koleini, K. K. Micinski, M. N. Rabe and C. Sánchez, "Temporal logics for hyperproperties", *Principles of Security and Trust (POST 2014)*, Lecture Notes in Computer Science 8414, Springer, 2014, pp. 265–284, extended version arXiv:1401.4492, <https://arxiv.org/abs/1401.4492>: Section 6, Theorem 5 and its proof.
