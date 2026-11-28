# Observation marginal mass as a real number

Let $h$ be a hidden Markov model with finite state set $S$, finite observation set $O$ and real weights: initial weights $\pi(s)$, transition weights $a(s, s')$ and emission weights $b(s, o)$. Assume $h$ is normalized: $\pi \ge 0$ with $\sum_s \pi(s) = 1$, $a \ge 0$ with $\sum_{s'} a(s, s') = 1$ for every $s$, and $b \ge 0$ with $\sum_o b(s, o) = 1$ for every $s$ (zero entries allowed). For every $t \in \mathbb{N}$ and observation string $x = (x_0, \dots, x_t)$, the real value of the observation-marginal mass of the joint distribution at $x$ equals the likelihood of $x_0, \dots, x_t$:

$$\Pr[X = x] = \sum_{z \in S^{t+1}} \pi(z_0)\, b(z_0, x_0) \prod_{k=1}^{t} a(z_{k-1}, z_k)\, b(z_k, x_k) .$$
