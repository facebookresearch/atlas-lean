# Clause learning as a proof system

The clause-learning algorithm CLR keeps a [SAT state](unit-resolution-and-sat-solver-states.md) $(\Delta, \Gamma, D)$, starting from $\Gamma = \mathrm{true}$ and $D = \langle\rangle$. If the state is 1-inconsistent, it returns unsatisfiable when $D$ is empty, and otherwise adds the [asserting clause](conflict-clauses-and-asserting-clauses.md) $\alpha$ chosen by its learning scheme to $\Gamma$ and backtracks to the first $m$ decisions, $m$ the assertion level of $\alpha$. Otherwise it may restart, setting $D$ to $\langle\rangle$, and then extends $D$ by a literal that is neither implied nor falsified by unit resolution, returning $D$ as a model when there is none. An *extended branching sequence*, a sequence of literals and restart symbols, fixes the decisions and restarts.

Viewing each learned clause as derived by a resolution derivation from the input and earlier learned clauses, and the final conflict as a unit-resolution refutation, a run on an unsatisfiable $\Delta$ yields a resolution refutation of $\Delta$. For a learning scheme LS, the proof system $\mathrm{CLR}_{\mathrm{LS}}$ consists of all refutations generated in this way. A proof system *p-simulates* another if, for every unsatisfiable formula, its shortest refutation is at most polynomially longer than the shortest refutation in the other.

## Depends on

- [Conflict clauses and asserting clauses](conflict-clauses-and-asserting-clauses.md)
- [Resolution derivability](../resolution/resolution-derivable.md)

## Sources

- K. Pipatsrisawat and A. Darwiche, "On the power of clause-learning SAT solvers as resolution engines", *Artificial Intelligence* 175(2):512–525, 2011, <http://reasoning.cs.ucla.edu/fetch.php?id=101&type=pdf>, Section 2.1 (Definition 1, resolution proofs, and Definition 2, p-simulation), Section 3.1 (Algorithm 1), Section 3.3 (extended branching sequences) and Section 3.4 (Definition 5, the proof system $\mathrm{CLR}_{\mathrm{LS}}$).
