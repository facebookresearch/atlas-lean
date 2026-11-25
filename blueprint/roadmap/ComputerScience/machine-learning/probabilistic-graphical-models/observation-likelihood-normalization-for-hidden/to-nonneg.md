# Normalized hidden Markov models have nonnegative weights

Let $h$ be a hidden Markov model with finite state set $S$, finite observation set $O$ and real weights: initial weights $\pi(s)$, transition weights $a(s, s')$ and emission weights $b(s, o)$. Assume $h$ is normalized: $\pi \ge 0$ with $\sum_s \pi(s) = 1$, $a \ge 0$ with $\sum_{s'} a(s, s') = 1$ for every $s$, and $b \ge 0$ with $\sum_o b(s, o) = 1$ for every $s$ (zero entries allowed).

Then all weights of $h$ are nonnegative: $\pi(s) \ge 0$, $a(s, s') \ge 0$ and $b(s, o) \ge 0$ for all states $s, s'$ and observations $o$.
