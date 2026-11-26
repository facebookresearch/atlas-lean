# Phase saving

**Phase saving** stores for each variable a **saved phase** $\mathrm{ph}(x) \in \{0, 1\}$, initially $0$. Whenever a backjump unassigns a variable $x$, its saved phase becomes the value $x$ had on the trail; a later decision on $x$ assigns $\mathrm{ph}(x)$. The polarity choice does not affect soundness or termination of abstract DPLL with learning, since any polarity is admitted by the Decide rule.

## Depends on

- [Abstract DPLL with learning](../../../Logic/propositional-logic/sat-solving/abstract-dpll-with-learning.md)

## Sources

- K. Pipatsrisawat and A. Darwiche, "A Lightweight Component Caching Scheme for Satisfiability Solvers", Theory and Applications of Satisfiability Testing (SAT 2007), LNCS 4501, Springer, 2007.
- N. Eén and N. Sörensson, "An Extensible SAT-solver", Theory and Applications of Satisfiability Testing (SAT 2003), LNCS 2919, Springer, 2004.
