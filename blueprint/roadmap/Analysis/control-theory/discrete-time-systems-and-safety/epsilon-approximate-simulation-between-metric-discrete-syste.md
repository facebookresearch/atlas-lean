# epsilon-approximate simulation between metric discrete systems

This node collects approximate simulation relations between discrete systems and the safety transfer they give.

## Expansion

A sound expansion has separate pages for:

1. **Input-matched approximate simulation.** For systems $A = (X_A, U, f_A)$ and $B = (X_B, U, f_B)$ with states in a common
   metric space, $R \subseteq X_A \times X_B$ such that $(x, y) \in R$ implies $d(x, y) \le \varepsilon$ and
   $(f_A(x, u), f_B(y, u)) \in R$ for every input $u$.
2. **Alternating approximate simulation,** in which for every input of one system there is an input of the other whose
   successors stay related, with the full quantifier order of the controller-refinement page; it is not the input-matched
   notion.
3. **Safety transfer.** If $R$ is an input-matched approximate simulation, every initial state of $A$ is related to an initial
   state of $B$, and no trajectory of $B$, under any input word, enters the closed $\varepsilon$-thickening $\{y : \exists b \in \mathrm{Bad},\ d(y, b) \le \varepsilon\}$ of
   an unsafe set, then no trajectory of $A$ enters $\mathrm{Bad}$ (trajectories of $A$ and $B$ driven by the same input word
   from related initial states stay related).

## Depends on

- [Discrete-time dynamical system (input-driven state-update map)](discrete-time-dynamical-system.md)
- [Reachable sets, forward invariants and safety for discrete dynamics](reachable-sets-forward-invariants-and-safety-for-discrete-dy.md)

## Sources

- Overview of Logical Foundations of Cyber-Physical Systems — A. Platzer, Carnegie Mellon University (arXiv 1910.11232). <https://arxiv.org/pdf/1910.11232> Sec. 5 (transfer of model-level safety guarantees to executions), as background.
