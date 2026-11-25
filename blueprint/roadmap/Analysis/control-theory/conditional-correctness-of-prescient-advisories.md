# Conditional correctness of prescient advisories (safety case)

This node collects the prescient-advisory construction for human-in-the-loop controllers on finite game structures.

## Expansion

A sound expansion has separate pages for:

1. **Model.** A GR(1) specification $\psi = \psi^{\mathrm{env}} \to \psi^{\mathrm{sys}}$ over finite environment-input and system-output variables, its game
   structure and, when $\psi$ is unrealizable, a counterstrategy graph and its condensation into a directed acyclic graph; one step is one
   edge (a synchronous environment-input and system-output move). A labelling of the controller's states marks the failure-prone ones, as
   defined in the source.
2. **Definitions.** The monitoring, minimally intervening (for a cost on the cut environment edges), $T$-prescient and conditionally
   correct criteria of the linked criteria page, for a response time $T \ge 1$ in steps, and the mined environment assumptions: a minimum-cost
   set of condensed edges computed as an $s$-$t$ minimum cut between the source and terminal nodes of the condensed graph after deleting the
   nodes that reach a failure-prone node within $T - 1$ steps.
3. **Conditional guarantee.** Li, Sadigh, Sastry and Seshia, Theorem 1: for a GR(1) specification and $T \ge 1$, the construction yields either a fully
   autonomous controller satisfying $\psi$ (when $\psi$ is realizable) or a human-in-the-loop controller, composed of an automatic controller,
   the human operator and an advisory controller that raises an advisory exactly when a mined assumption is violated, which is monitoring,
   $T$-prescient, minimally intervening for the cost of the cut edges and conditionally correct; this assumes a single counterstrategy graph,
   an optimal counterstrategy (one that forces a violation as quickly as possible) and that every failure-prone node is at least $T$ steps
   from every initial node.
4. **Limitation.** Against an unrestricted environment the winning region is a trap, so refining it by "cannot be forced out within $T$
   steps" leaves it unchanged; the advisory then signals loss of the winning region without a guaranteed $T$-step warning.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Attractors, reachability and safety games.
- Statement prerequisite: GR(1) games, realizability and counterstrategies.

## Depends on

- [Advisory and handoff criteria for human-in-the-loop controllers](advisory-handoff-contract-criteria.md)
- [Human-in-the-loop controller model](human-in-the-loop-controller-model.md)

## Related topics

- [Interactive device state machines](../../ComputerScience/program-logics-and-verification/interactive-device-state-machines.md)

## Sources

- Synthesis for Human-in-the-Loop Control Systems — Li, Sadigh, Sastry, Seshia, TACAS 2014, Section 3.3 (criteria), Section 5 (assumption mining by minimum cut) and Theorem 1 with footnotes 6–7. <https://sites.bu.edu/depend/files/2017/02/hilp-tacas14.pdf>
