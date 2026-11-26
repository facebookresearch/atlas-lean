# Joint distribution of a normalized hidden Markov model

Let $h$ be a hidden Markov model with finite state set $S$, finite observation set $O$ and real weights: initial weights $\pi(s)$, transition weights $a(s, s')$ and emission weights $b(s, o)$. Assume $h$ is normalized: $\pi \ge 0$ with $\sum_s \pi(s) = 1$, $a \ge 0$ with $\sum_{s'} a(s, s') = 1$ for every $s$, and $b \ge 0$ with $\sum_o b(s, o) = 1$ for every $s$ (zero entries allowed).

The joint distribution at horizon $t$ is the probability mass function on pairs of a hidden path $z \in S^{t+1}$ and an observation string $x \in O^{t+1}$ obtained by drawing $z$ from the hidden-path distribution and then $x$ from the observation distribution given $z$.
