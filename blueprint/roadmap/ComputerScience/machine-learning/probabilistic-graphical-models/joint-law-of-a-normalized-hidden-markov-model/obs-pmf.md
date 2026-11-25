# Observation distribution given a hidden path

Let $h$ be a hidden Markov model with finite state set $S$, finite observation set $O$ and real weights: initial weights $\pi(s)$, transition weights $a(s, s')$ and emission weights $b(s, o)$. Assume $h$ is normalized: $\pi \ge 0$ with $\sum_s \pi(s) = 1$, $a \ge 0$ with $\sum_{s'} a(s, s') = 1$ for every $s$, and $b \ge 0$ with $\sum_o b(s, o) = 1$ for every $s$ (zero entries allowed).

For a horizon $t$ and a hidden path $z = (z_0, \dots, z_t)$, the observation distribution is the probability mass function on strings $(x_0, \dots, x_t) \in O^{t+1}$ in which each $x_i$ is drawn from the emission distribution $b(z_i, \cdot)$, independently across times; it is defined by recursion on $t$, appending one emission per step.
