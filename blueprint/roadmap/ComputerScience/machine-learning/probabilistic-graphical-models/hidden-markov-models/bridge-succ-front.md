# Front decomposition of the bridge weights

Let $h$ be a hidden Markov model with finite
state set $S$, transition weights $a$ and emission weights $b$ in a semiring, let $x_0, x_1, \dots$
be observations, and write $B_k(t, s, u)$ for the bridge weight of the paths from state $s$ at
time $t$ to state $u$ at time $t + k$. Then for all $k, t \in \mathbb{N}$ and $s, u \in S$,

$$B_{k+1}(t, s, u) = \sum_{s' \in S} a(s, s')\, b(s', x_{t+1})\, B_k(t + 1, s', u).$$
