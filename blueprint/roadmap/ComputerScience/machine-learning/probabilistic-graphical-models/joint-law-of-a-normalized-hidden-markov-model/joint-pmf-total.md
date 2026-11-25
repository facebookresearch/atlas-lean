# Joint distribution of a hidden Markov model has total mass one

Let $h$ be a hidden Markov model with finite state set $S$, finite observation set $O$ and real weights: initial weights $\pi(s)$, transition weights $a(s, s')$ and emission weights $b(s, o)$. Assume $h$ is normalized: $\pi \ge 0$ with $\sum_s \pi(s) = 1$, $a \ge 0$ with $\sum_{s'} a(s, s') = 1$ for every $s$, and $b \ge 0$ with $\sum_o b(s, o) = 1$ for every $s$ (zero entries allowed). For every horizon $t$, the masses of the joint distribution on pairs of paths and observation strings of length $t + 1$ sum to one:

$$\sum_{(z, x) \in S^{t+1} \times O^{t+1}} \Pr[(Z, X) = (z, x)] = 1 .$$
