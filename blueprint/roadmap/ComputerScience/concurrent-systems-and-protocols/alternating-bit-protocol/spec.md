# Recursive specification of the data-free alternating-bit protocol

The process constants
are the states of the five agents: the sender, the data channel, the receiver, the
acknowledgement channel and the one-place buffer. For a state $x$ of one of these agents, let
$(a_1, x_1), \dots, (a_n, x_n)$ be the transitions of $x$ as listed by the transition function
of its agent, let $X_i$ be the constant of the same agent at state $x_i$, and let $\mathbf{0}$
be the inactive process. The specification defines the constant of $x$ as the choice of
prefixes $a_1.X_1 + (a_2.X_2 + \cdots + (a_n.X_n + \mathbf{0}))$.
