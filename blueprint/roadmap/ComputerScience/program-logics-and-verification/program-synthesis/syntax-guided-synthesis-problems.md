# Syntax-guided synthesis problems

A syntax-guided synthesis (SyGuS) instance consists of a background first-order theory $T$, a function symbol $f$ of arity $k$ with argument sorts $\sigma_1, \dots, \sigma_k$ and result sort $\sigma$, formal parameters $y_1, \dots, y_k$ of those sorts, a context-free grammar $G$ whose language $L(G)$ is a set of terms of sort $\sigma$ over the signature of $T$ and the parameters $\bar y$, and a specification $\varphi(f, \bar x)$, a formula of $T$ extended with $f$. A *solution* is a term $e \in L(G)$ such that $T \models \forall \bar x.\, \varphi(e, \bar x)$, where $\varphi(e, \bar x)$ is obtained by replacing every application $f(t_1, \dots, t_k)$ by the capture-avoiding substitution $e[t_1/y_1, \dots, t_k/y_k]$.

## Depends on

- [Background theories in typed first-order logic](../../../Logic/first-order-logic/background-theories-in-typed-first-order-logic.md)
- [Language generated from a nonterminal](../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/context-free-grammars/language-from.md)

## Sources

- R. Alur, R. Bodik, G. Juniwal, M. M. K. Martin, M. Raghothaman, S. A. Seshia, R. Singh, A. Solar-Lezama, E. Torlak and A. Udupa, "Syntax-guided synthesis", *FMCAD 2013*, IEEE, 2013
