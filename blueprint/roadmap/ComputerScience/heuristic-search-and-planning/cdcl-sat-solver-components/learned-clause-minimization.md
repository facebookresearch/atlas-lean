# Recursive minimization of learned clauses

Let $D$ be a clause learned by conflict analysis, all of whose literals are false under the trail $M$. A literal $y \in D$ is **redundant** (with respect to $D$ and $M$) if $\neg y$ is an implied literal of $M$ with reason clause $R$, and every literal of $R$ other than $\neg y$ is either in $D$ or, recursively, redundant. **Recursive minimization** removes every redundant literal from $D$; **basic minimization** recurses only into literals implied at decision level $0$.

## Depends on

- [Abstract DPLL with learning](../../../Logic/propositional-logic/sat-solving/abstract-dpll-with-learning.md)
- [RUP and RAT clauses](../../../Logic/propositional-logic/proof-certificates/rup-and-rat-clauses.md)

## Sources

- N. Sörensson and A. Biere, "Minimizing Learned Clauses", Theory and Applications of Satisfiability Testing (SAT 2009), LNCS 5584, Springer, 2009.
- N. Eén and N. Sörensson, "An Extensible SAT-solver", Theory and Applications of Satisfiability Testing (SAT 2003), LNCS 2919, Springer, 2004.
