# Satisfiability of LTLf modulo theories is undecidable

Satisfiability of linear temporal logic over finite data words with embedded first-order data constraints is undecidable, already when the data constraints are quantifier-free linear integer arithmetic, a decidable theory.

**Theorem (Faella and Parlato).** Fix a many-sorted first-order data logic $\mathcal D$ with constants, functions and relations, and a data signature $S$ of typed fields. A *data word* is a finite sequence of symbols, each assigning a value of the right sort to every field of $S$. Terms of $\mathrm{LTL}_f^{\mathrm{MT}}$ are

$$
t ::= \bigcirc^n\mathit{id} \mid \sim^n\mathit{id} \mid c \mid f(t_1, \ldots, t_k), \qquad \varphi ::= p(t_1, \ldots, t_k) \mid \neg\varphi \mid \varphi \wedge \varphi \mid \varphi\,\mathsf U\,\varphi \mid \mathsf X\varphi,
$$

with $n \ge 0$, fields $\mathit{id}$ of $S$, constants $c$, function symbols $f$ and relation symbols $p$ of $\mathcal D$. On a data word $w$, $\bigcirc^n\mathit{id}$ denotes the value of $\mathit{id}$ $n$ symbols ahead and is a *strong error* if the word is too short, while $\sim^n\mathit{id}$ denotes the same value and is a *weak error* if the word is too short; errors propagate through functions with strong errors taking priority. An atom $p(t_1, \ldots, t_k)$ is false if some term is a strong error, true if otherwise some term is a weak error, and otherwise evaluated in $\mathcal D$; $\mathsf X\varphi$ requires a next symbol, and $\neg$, $\wedge$, $\mathsf U$ are as in LTL over finite words. The *satisfiability problem* asks, given a formula $\varphi$ with its data signature, whether some data word satisfies $\varphi$. This problem is undecidable (Theorem 1 of the source); the proof takes $\mathcal D$ to be quantifier-free linear integer arithmetic.

$\mathrm{LTL}_f^{\mathrm{MT}}$ is the quantifier-free fragment of the LTLf modulo theories of Geatti, Gianola and Gigante and extends the logic of Felli, Montali, Patrizi and Winkler by more general data constraints. The source reduces satisfiability to emptiness of symbolic data-word automata and then to constrained Horn clauses, which off-the-shelf solvers often settle despite the undecidability.

## Depends on

- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

For a two-counter machine, data words have two fields of type $\mathbb N$ for the counters and an enumeration field for the current instruction, one symbol per configuration. Atoms relating $\mathit{id}$ and $\bigcirc^1\mathit{id}$, under $\mathsf G$, force consecutive symbols to be consecutive configurations, and a further formula requires the halting instruction to occur. Such a formula is satisfiable iff the machine halts. Over a data logic with a finite domain, satisfiability becomes equivalent to that of standard LTLf and is decidable.

## Sources

- M. Faella and G. Parlato, "A Unified Automata-Theoretic Approach to LTLf Modulo Theories", in *ECAI 2024*, Frontiers in Artificial Intelligence and Applications 392, IOS Press, 2024, <https://doi.org/10.3233/FAIA240622>; read as arXiv:2408.08817v1, <https://arxiv.org/abs/2408.08817v1>: Section 2 (data words, data logic), Section 3 (syntax and semantics of $\mathrm{LTL}_f^{\mathrm{MT}}$, Theorem 1), Section 4.1 (emptiness of symbolic data-word automata via constrained Horn clauses) and Appendix A (proof of Theorem 1).
