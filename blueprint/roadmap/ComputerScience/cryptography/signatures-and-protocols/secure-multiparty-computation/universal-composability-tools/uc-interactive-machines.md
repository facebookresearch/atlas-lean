# Interactive machines, linking and the single-token execution model

An *interactive machine* $M$ with imported interface $I$ and exported interface $E$ is a stateful probabilistic program: it samples a private initial state, and each *activation* answers one query of $E$, possibly making calls to $I$ and updating its state. *Linking* $A \circ P$ answers the imports of $A$ by the exports of $P$; running a program against $A \circ P$ is running it against $A$ and running the resulting calls against $P$, so linking is associative and a state representation commuting with every activation commutes with every run. In the *single-token push model* of execution, a system of reactive machines passes one activation token: at each scheduler step the active machine either sends a message to one machine (activating it), returns output or halts; halted machines stay halted, the log only grows, one step makes at most one network query, and a run of $s$ steps activates machines at most $s$ times. An *ideal functionality* is a machine with party ports and an adversary port; a *hybrid functionality* additionally has a private outgoing call port to a resource.

## Depends on

- [UC emulation](../uc-emulation.md)
- [Packages and composition in state-separating proofs](../../../security-games/state-separating-proofs/ssp-packages.md)

## Sources

- Ran Canetti, "Universally Composable Security", Journal of the ACM, 2020.
