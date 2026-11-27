# Recursive minimization of learned clauses

Let $D$ be a clause learned by conflict analysis, all of whose literals are false under the trail $M$. A literal $y \in D$ is **redundant** (with respect to $D$ and $M$) if $\neg y$ is an implied literal of $M$ with reason clause $R$, and every literal of $R$ other than $\neg y$ is either in $D$ or, recursively, redundant. Literals false at decision level $0$ may be treated as redundant as well. **Recursive minimization** removes every redundant literal from $D$; **local minimization** removes only those $y$ for which every literal of $R$ other than $\neg y$ is already in $D$ (or false at level $0$), without recursion.

## Depends on

- [Abstract DPLL with learning](../../../Logic/propositional-logic/sat-solving/abstract-dpll-with-learning.md)

## Sources

- N. Sörensson and A. Biere, "Minimizing Learned Clauses", Theory and Applications of Satisfiability Testing (SAT 2009), LNCS 5584, Springer, 2009, Section 2 (local and recursive minimization).
