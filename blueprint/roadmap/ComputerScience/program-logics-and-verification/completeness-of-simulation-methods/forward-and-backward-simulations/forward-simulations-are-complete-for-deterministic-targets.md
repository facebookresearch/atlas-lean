# Forward simulations are complete for deterministic targets

If $B$ is a deterministic automaton and $A \le_{\ast T} B$, then there is a [forward simulation](forward-simulations-are-sound.md) from $A$ to $B$. One is the relation that relates a state $s$ of $A$ to the state of $B$ reached by the trace of each finite execution of $A$ leading to $s$.

## Depends on

- [Forward simulations are sound for trace inclusion](forward-simulations-are-sound.md)

## Sources

- N. Lynch and F. Vaandrager, "Forward and backward simulations, Part I: Untimed systems", *Information and Computation* 121(2):214–233, 1995; author version of the journal paper, October 31, 1994, <https://groups.csail.mit.edu/tds/papers/Lynch/IC95.pdf>, Section 3.2, Theorem 3.11.
