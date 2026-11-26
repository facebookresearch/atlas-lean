# Observation marginal of the joint distribution is the likelihood

Let $h$ be a hidden Markov model with finite state set $S$, finite observation set $O$ and real weights: initial weights $\pi(s)$, transition weights $a(s, s')$ and emission weights $b(s, o)$. Assume $h$ is normalized: $\pi \ge 0$ with $\sum_s \pi(s) = 1$, $a \ge 0$ with $\sum_{s'} a(s, s') = 1$ for every $s$, and $b \ge 0$ with $\sum_o b(s, o) = 1$ for every $s$ (zero entries allowed). For every $t \in \mathbb{N}$ and observation string $x = (x_0, \dots, x_t)$, the observation marginal of the joint distribution at horizon $t$ has mass

$$\Pr[X = x] = \mathcal{L}_t(\bar x) = \sum_{z \in S^{t+1}} P(z, x)$$

at $x$, as an element of $[0, \infty]$, where $\mathcal{L}_t$ is the likelihood of $x_0, \dots, x_t$.
