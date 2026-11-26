# Hidden-path distribution of a normalized hidden Markov model

Let $h$ be a hidden Markov model with finite state set $S$, finite observation set $O$ and real weights: initial weights $\pi(s)$, transition weights $a(s, s')$ and emission weights $b(s, o)$. Assume $h$ is normalized: $\pi \ge 0$ with $\sum_s \pi(s) = 1$, $a \ge 0$ with $\sum_{s'} a(s, s') = 1$ for every $s$, and $b \ge 0$ with $\sum_o b(s, o) = 1$ for every $s$ (zero entries allowed).

The hidden-path distribution at horizon $t$ is the probability mass function on paths $z = (z_0, \dots, z_t) \in S^{t+1}$ defined by recursion on $t$: at $t = 0$, draw $z_0$ from the initial distribution $\pi$; at $t + 1$, draw a path $(z_0, \dots, z_t)$ at horizon $t$ and then $z_{t+1}$ from the transition distribution $a(z_t, \cdot)$, and return $(z_0, \dots, z_{t+1})$.
