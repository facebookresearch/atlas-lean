# Pair hidden Markov model

A pair HMM (Durbin et al. 1998) over an alphabet $A$ with weights in a set $R$ consists of

- weights $\pi_0(s)$ of the transitions from the silent begin state to the [emitting states](pair-state.md) $s$, and a weight $\tau_0$ of the transition from the begin state directly to the silent end state;
- weights $t(s, s')$ of the transitions between emitting states;
- weights $\tau(s)$ of the transitions from emitting states to the end state;
- emission weights $e_M(a, b)$, $e_X(a)$ and $e_Y(b)$ of the three emitting states.

## Sources

- R. Durbin, S. R. Eddy, A. Krogh and G. Mitchison, *Biological Sequence Analysis: Probabilistic Models of Proteins and Nucleic Acids*, Cambridge University Press (1998).
