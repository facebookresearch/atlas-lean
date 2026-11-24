# Syntax-guided synthesis problems

A syntax-guided synthesis (SyGuS) instance consists of a background first-order theory $T$, a function symbol $f$ with a given type, a context-free grammar $G$ whose language $L(G)$ is a set of terms over the signature of $T$ of the type of $f$, and a specification $\varphi(f, \bar x)$, a formula of $T$ extended with $f$. A *solution* is a term $e \in L(G)$ such that $T \models \forall \bar x.\, \varphi(e, \bar x)$, where $\varphi(e, \bar x)$ is obtained by substituting $e$ for $f$.

## Depends on

- [Background theories in typed first-order logic](../../../Logic/first-order-logic/background-theories-in-typed-first-order-logic.md)
- [Language generated from a nonterminal](../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/context-free-grammars/language-from.md)

## Sources

- R. Alur, R. Bodik, G. Juniwal, M. M. K. Martin, M. Raghothaman, S. A. Seshia, R. Singh, A. Solar-Lezama, E. Torlak and A. Udupa, "Syntax-guided synthesis", *FMCAD 2013*, IEEE, 2013
