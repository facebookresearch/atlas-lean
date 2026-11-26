# Backward simulations are complete for forest sources

If the automaton $A$ is a forest and $A \le_{\ast T} B$, then $A \le_B B$; if moreover $B$ has finite invisible nondeterminism, then $A \le_{iB} B$. A [backward simulation](backward-simulations-are-sound.md) relates each state $s$ of $A$, reached by a unique execution with trace $\beta$, to the states of $B$ reached by executions with trace $\beta$ none of whose proper prefixes has trace $\beta$.

## Depends on

- [Backward simulations are sound for trace inclusion](backward-simulations-are-sound.md)

## Sources

- N. Lynch and F. Vaandrager, "Forward and backward simulations, Part I: Untimed systems", *Information and Computation* 121(2):214–233, 1995; author version of the journal paper, October 31, 1994, <https://groups.csail.mit.edu/tds/papers/Lynch/IC95.pdf>, Section 3.3, Theorem 3.18.
