# Profile hidden Markov model

A profile HMM with $L$ consensus columns over an alphabet $A$ with weights in a set $R$ consists of

- transition weights $t_k(s, s')$ from the state of [type](profile-state.md) $s$ at node $k$ ($0 \le k \le L$; node $0$ is the begin state, read as type $M$) to a state of type $s'$: to $M$ or $D$ at node $k + 1$, or to $I$ at node $k$;
- weights $\tau(s)$ of the transitions from the state of type $s$ at node $L$ to the end state;
- match emission weights $e^M_k(a)$ and insert emission weights $e^I_k(a)$ for nodes $k$ and residues $a$.
