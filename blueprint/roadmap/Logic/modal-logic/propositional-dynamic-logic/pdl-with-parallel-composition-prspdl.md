# PDL with parallel composition (PRSPDL)

PRSPDL is propositional dynamic logic over states that can be split into two components: besides atomic programs, tests and iteration it has programs that recover or store a component of a composite state and a parallel composition $\alpha \parallel \beta$ that runs $\alpha$ and $\beta$ on the two components; it lacks a choice operator.

**Syntax.** Formulas and program terms are defined simultaneously:

$$
\varphi ::= p \mid \bot \mid (\varphi \to \varphi) \mid [\alpha]\varphi, \qquad \alpha ::= a \mid r_1 \mid r_2 \mid s_1 \mid s_2 \mid \varphi? \mid (\alpha ; \alpha) \mid (\alpha \parallel \alpha) \mid \alpha^*,
$$

with $p$ a propositional variable and $a$ an atomic program term.

**Models.** A model is $\mathcal{M} = (S, \{R_a\}_a, \ast, V)$ with a nonempty set $S$ of states, a relation $R_a$ for each atomic program, a function $\ast : S \times S \to 2^S$ (where $s \in x \ast y$ means that $s$ is a composition of $x$ and $y$) and a valuation $V$. Tests, composition and iteration are as in PDL, and

- $(s, t) \in R_{\alpha \parallel \beta}$ iff $s \in x_1 \ast x_2$, $t \in y_1 \ast y_2$, $(x_1, y_1) \in R_\alpha$ and $(x_2, y_2) \in R_\beta$ for some $x_1, x_2, y_1, y_2$;
- $(s, t) \in R_{r_1}$ iff $s \in t \ast u$ for some $u$, and $(s, t) \in R_{r_2}$ iff $s \in u \ast t$ for some $u$;
- $(s, t) \in R_{s_1}$ iff $t \in s \ast u$ for some $u$, and $(s, t) \in R_{s_2}$ iff $t \in u \ast s$ for some $u$.

These are the *$\ast$-separated* models, with no further condition on $\ast$. Satisfiability and validity are as for PDL. The *variable-free fragment* consists of the formulas without propositional variables, built from $\bot$ alone.

## Depends on

- [Kripke model](../kripke-semantics/kripke-model.md)
- [PDL formulas](propositional-dynamic-logic-pdl/formula.md)
- [PDL programs](propositional-dynamic-logic-pdl/program.md)
- [PDL model](propositional-dynamic-logic-pdl/model.md)

## Proof depends on

None.

## Expansion

Balbiani and Tinchev introduced the logic and several variants that differ in the conditions imposed on $\ast$; satisfiability of PRSPDL is undecidable. Regular PDL is EXPTIME-complete and PDL with intersection 2EXPTIME-complete, and for all three logics the variable-free fragment is as hard as the whole logic.

## Sources

- M. Rybakov and D. Shkatov, "Complexity and expressivity of propositional dynamic logics with finitely many variables", *Logic Journal of the IGPL* 26(5):539–547, 2018, doi:10.1093/jigpal/jzy014; read as arXiv:1901.06407v1, <https://arxiv.org/abs/1901.06407v1>: Section 2 (syntax and semantics of IPDL, PDL and PRSPDL over $\ast$-separated models, and variable-free fragments).
