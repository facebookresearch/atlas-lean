# Profile HMM as an alignment automaton

A [profile HMM](profile-hmm.md) with weights in a semiring gives the [alignment automaton](../pair-hidden-markov-models/alignment-automaton.md) reading alignments of a sequence to the [columns](columns.md), whose control states are pairs $(s, k)$ of a state type and the current node, with

- column weights $t_k(s, M)\, e^M_j(a)$ for $(a, j)$, $t_k(s, I)\, e^I_k(a)$ for $(a, -)$, $t_k(s, D)$ for $(-, j)$, and $0$ for $(-, -)$, in control state $(s, k)$;
- next control states $(M, j)$, $(I, k)$, $(D, j)$ and $(s, k)$ respectively;
- final weight $\tau(s)$ in control state $(s, k)$.
