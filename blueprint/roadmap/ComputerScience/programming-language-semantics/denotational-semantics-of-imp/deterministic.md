# The denotational semantics of IMP is deterministic

For every IMP command $c$ and all
states $s$, $s_1$ and $s_2$, if the relational denotation of $c$ relates $s$ to $s_1$ and $s$
to $s_2$, then $s_1 = s_2$.

The proof goes through the agreement with the deterministic big-step semantics.
