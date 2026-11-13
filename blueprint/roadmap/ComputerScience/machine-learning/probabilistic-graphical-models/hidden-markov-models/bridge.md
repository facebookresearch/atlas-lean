# Bridge weights of a hidden Markov model

Let $h$ be a hidden Markov model with finite state
set $S$, transition weights $a$ and emission weights $b$ in a semiring $R$, and let
$x_0, x_1, \dots$ be observations. The bridge weights $B_k(t, s, u) \in R$, for
$k, t \in \mathbb{N}$ and $s, u \in S$, are defined from the end by $B_0(t, s, u) = 1$ if $s = u$
and $B_0(t, s, u) = 0$ otherwise, and

$$B_{k+1}(t, s, u) = \left(\sum_{u' \in S} B_k(t, s, u')\, a(u', u)\right) b(u, x_{t+k+1}).$$

Thus $B_k(t, s, u)$ is the total weight of the paths from state $s$ at time $t$ to state $u$ at
time $t + k$, with transitions and emissions at times $t + 1, \dots, t + k$.
