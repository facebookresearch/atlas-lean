# Running against a stateful randomized oracle

A stateful randomized oracle with states in a set $\Sigma$ answers a query $x$ in state $s$ by
drawing an answer and a new state from a distribution $O(s, x)$. Running an oracle computation
against $O$ from a state $s$ gives the distribution of its output and final state: a computation
that stops with output $a$ gives $(a, s)$, and one that asks $x$ draws $(y, s')$ from $O(s, x)$ and
continues on the answer $y$ from the state $s'$. This is oracle access to a stateful algorithm, such
as a lazily sampled random oracle (Katz and Lindell, Section 5.5.1).
