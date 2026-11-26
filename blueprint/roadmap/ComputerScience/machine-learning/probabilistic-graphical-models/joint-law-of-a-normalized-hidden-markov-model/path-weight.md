# Prior weight of a hidden path

Let $h$ be a hidden Markov model with state set $S$, observation set $O$ and real weights: initial weights $\pi(s)$, transition weights $a(s, s')$ and emission weights $b(s, o)$. For $t \in \mathbb{N}$ and a path $z = (z_0, \dots, z_t)$, the prior weight of $z$ is

$$w(z) = \pi(z_0) \prod_{i=0}^{t-1} a(z_i, z_{i+1}) \in \mathbb{R}.$$
