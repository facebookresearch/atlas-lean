# Initial-state distribution of a normalized hidden Markov model

Let $h$ be a hidden Markov model with finite state set $S$, finite observation set $O$ and real weights: initial weights $\pi(s)$, transition weights $a(s, s')$ and emission weights $b(s, o)$. Assume $h$ is normalized: $\pi \ge 0$ with $\sum_s \pi(s) = 1$, $a \ge 0$ with $\sum_{s'} a(s, s') = 1$ for every $s$, and $b \ge 0$ with $\sum_o b(s, o) = 1$ for every $s$ (zero entries allowed).

The initial-state distribution is the probability mass function on $S$ given by $s \mapsto \pi(s)$ (as an element of $[0, \infty]$); it has total mass one by normalization.
