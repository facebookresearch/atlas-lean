# Abstraction-based controller synthesis soundness

This node collects controller refinement from a finite abstraction through an alternating approximate simulation.

## Expansion

A sound expansion has separate pages for:

1. **Alternating approximate simulation.** For a concrete system $A$ and an abstract system $B$ with outputs in a common
   metric space, a relation $R$ such that related states have outputs within $\varepsilon$, and for every related pair and
   every abstract input enabled at the abstract state there is a concrete input enabled at the concrete state (one with at
   least one successor) such that every concrete successor (for every disturbance) is related to some abstract successor;
   every concrete initial state is related to some abstract initial state.
2. **Controller refinement.** If a controller for $B$ chooses only enabled inputs and keeps every trajectory of $B$ infinite
   and inside the safe set shrunk by $\varepsilon$ (outputs at distance more than $\varepsilon$ from the unsafe set), then the
   refined controller, which tracks a related abstract state and chooses an enabled concrete input through the relation,
   keeps every trajectory of $A$ infinite and inside the safe set. Without the enabledness requirement a blocking concrete
   input satisfies the successor condition vacuously, and the refined loop can deadlock.
3. The exact formulations of Tabuada and of Girard and Pappas, with their quantifier orders and relation directions, as
   the sources for these pages.

## Depends on

- [epsilon-approximate simulation between metric discrete systems](epsilon-approximate-simulation-between-metric-discrete-syste.md)

## Related topics

- [Maximal controlled invariant set and safety controllers on finite systems](maximal-controlled-invariant-set-and-safety-controllers-on-f.md)

## Sources

- Overview of Logical Foundations of Cyber-Physical Systems — A. Platzer, Carnegie Mellon University (arXiv 1910.11232). <https://arxiv.org/pdf/1910.11232> Sec. 5 (transfer of model-level safety guarantees to executions), as background.
