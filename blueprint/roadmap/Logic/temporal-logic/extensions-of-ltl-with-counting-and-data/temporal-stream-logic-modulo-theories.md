# Temporal stream logic modulo theories

Temporal stream logic (TSL) extends LTL with updates of cells by function terms and with predicate terms as atoms; interpreting its function and predicate symbols in the models of a first-order theory, such as equality, uninterpreted functions or Presburger arithmetic, defines satisfiability and validity modulo that theory.

**Syntax.** Fix a finite set $\mathbb{C}$ of *cells*, function symbols $\Sigma_F$ (constants included) and predicate symbols $\Sigma_P$. Function terms $\tau_f$ are built from cells by applying function symbols; predicate terms $\tau_p$ apply a predicate symbol to function terms. TSL formulas are

$$
\varphi, \psi ::= \mathit{true} \mid \neg\varphi \mid \varphi \wedge \psi \mid \mathbf{X}\varphi \mid \varphi\,\mathbf{U}\,\psi \mid \tau_p \mid [\![c \leftarrow \tau_f]\!],
$$

with $c \in \mathbb{C}$; $[\![c \leftarrow \tau_f]\!]$ is an *update* saying that the value of $\tau_f$ is assigned to cell $c$. $\mathbf{F}$ and $\mathbf{G}$ are defined as in LTL.

**Semantics.** A *computation* $\varsigma$ is an infinite sequence of assignments of a function term to each cell. A symbolic evaluation $\eta$ unfolds the value of a cell at time $t$ into a term over the initial cell values: $\eta(\varsigma, 0, c) = c$, $\eta(\varsigma, t, c) = \eta(\varsigma, t-1, \varsigma_{t-1}(c))$ for $t > 0$, and $\eta$ commutes with function symbols. An *execution* is a triple $(\varsigma, \mathcal{V}, \langle\cdot\rangle)$, where $\langle\cdot\rangle$ interprets cells (their initial values), function symbols and predicate symbols over a set of values $\mathcal{V}$. Updates hold syntactically ($\varsigma, t \models [\![c \leftarrow \tau]\!]$ iff $\varsigma_t(c) \equiv \tau$); a predicate term is true at $t$ iff its symbolic evaluation $\eta(\varsigma, t, \cdot)$ is true under $\langle\cdot\rangle$; $\mathbf{X}$ and $\mathbf{U}$ are as in LTL over $\omega$-sequences.

**Modulo a theory.** For a first-order theory $T$ over $\Sigma_F$, $\Sigma_P$, a TSL formula $\varphi$ is *satisfiable in $T$* if some execution satisfies $\varphi$ at time $0$ with $(\mathcal{V}, \langle\cdot\rangle)$ a model of $T$, and *valid in $T$* if every such execution does; $\varphi$ is satisfiable in $T$ iff $\neg\varphi$ is not valid in $T$. The theories considered are uninterpreted functions $T_U$ (no axioms), equality $T_E$, whose axioms make $=$ equality, and Presburger arithmetic $T_N$, whose axioms define the constants $0$ and $1$, equality and addition (Section 2 of the source).

## Depends on

- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)

## Proof depends on

None.

## Expansion

TSL was introduced by Finkbeiner, Klein, Piskac and Santolucito for reactive synthesis with uninterpreted functions and predicates, where inputs and outputs are distinguished; for satisfiability that distinction is irrelevant. A computation is *finitary* for $\varphi$ if every cell is at every step either kept or updated by one of the update terms of $\varphi$, which gives finitary satisfiability and validity.

## Sources

- Bernd Finkbeiner, Philippe Heim and Noemi Passing, "Temporal stream logic modulo theories", in *Foundations of Software Science and Computation Structures (FoSSaCS 2022)*, Lecture Notes in Computer Science 13242, Springer, 2022, pp. 325–346, doi:10.1007/978-3-030-99253-8_17; read as arXiv:2104.14988v2, <https://arxiv.org/abs/2104.14988v2>: Section 3 (TSL syntax and semantics, the definitions of TSL satisfiability and validity in a theory, the duality theorem and finitary computations) and Appendix A (first-order theories) of arXiv:2104.14988v2.
