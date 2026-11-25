# Hidden-path marginal mass is the prior weight

Let $h$ be a hidden Markov model with finite state set $S$, finite observation set $O$ and real weights: initial weights $\pi(s)$, transition weights $a(s, s')$ and emission weights $b(s, o)$. Assume $h$ is normalized: $\pi \ge 0$ with $\sum_s \pi(s) = 1$, $a \ge 0$ with $\sum_{s'} a(s, s') = 1$ for every $s$, and $b \ge 0$ with $\sum_o b(s, o) = 1$ for every $s$ (zero entries allowed). For every $t \in \mathbb{N}$ and path $z = (z_0, \dots, z_t)$, the hidden-path marginal of the joint distribution has mass

$$\Pr[Z = z] = \pi(z_0) \prod_{i=0}^{t-1} a(z_i, z_{i+1})$$

at $z$, as an element of $[0, \infty]$.
