# Pair HMM as an alignment automaton

A [pair HMM](pair-hmm.md) with weights in a semiring gives the [alignment automaton](alignment-automaton.md) whose control states are "begin" and the emitting states, with

- column weight $\pi_0(s_c)\, \epsilon(c)$ in the begin state and $t(s, s_c)\, \epsilon(c)$ in state $s$, where $s_c$ is the [state of the column](col-state.md) $c$ and $\epsilon$ the [emission weight](emit-col.md);
- next control state $s_c$;
- final weight $\tau_0$ in the begin state and $\tau(s)$ in state $s$.
