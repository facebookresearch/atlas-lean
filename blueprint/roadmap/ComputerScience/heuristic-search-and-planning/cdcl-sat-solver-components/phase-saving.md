# Phase saving

**Phase saving** (progress saving) stores for each variable a **saved phase** $\mathrm{ph}(x) \in \{0, 1\}$, initially a fixed default value (here $0$). Whenever a backjump or restart unassigns a variable $x$, whether $x$ was a decision or an implied literal, its saved phase becomes the value $x$ had on the trail; a later decision on $x$ assigns $\mathrm{ph}(x)$. The polarity choice does not affect soundness or termination of abstract DPLL with learning, since any polarity is admitted by the Decide rule.

## Depends on

- [Abstract DPLL with learning](../../../Logic/propositional-logic/sat-solving/abstract-dpll-with-learning.md)

## Sources

- K. Pipatsrisawat and A. Darwiche, "A Lightweight Component Caching Scheme for Satisfiability Solvers", Theory and Applications of Satisfiability Testing (SAT 2007), LNCS 4501, Springer, 2007, Section 5 (progress saving).
