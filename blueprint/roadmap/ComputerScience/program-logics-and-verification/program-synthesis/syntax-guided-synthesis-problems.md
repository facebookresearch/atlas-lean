# Syntax-guided synthesis problems

A syntax-guided synthesis (SyGuS) instance consists of a background first-order theory $T$, a function symbol $f$ with a given type, a context-free grammar $G$ whose language $L(G)$ is a set of terms over the signature of $T$ of the type of $f$, and a specification $\varphi(f, \bar x)$, a formula of $T$ extended with $f$. A *solution* is a term $e \in L(G)$ such that $T \models \forall \bar x.\, \varphi(e, \bar x)$, where $\varphi(e, \bar x)$ is obtained by substituting $e$ for $f$.

## Depends on

- [Language generated from a nonterminal](../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/context-free-grammars/language-from.md)

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: First-order signatures, terms, formulas, theories and semantic consequence.

## Sources

- R. Alur, R. Bodik, G. Juniwal, M. M. K. Martin, M. Raghothaman, S. A. Seshia, R. Singh, A. Solar-Lezama, E. Torlak and A. Udupa, "Syntax-guided synthesis", *FMCAD 2013*, IEEE, 2013
