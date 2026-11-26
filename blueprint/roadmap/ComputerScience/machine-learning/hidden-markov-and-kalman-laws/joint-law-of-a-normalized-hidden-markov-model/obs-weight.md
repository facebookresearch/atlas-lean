# Observation weight of a string given a hidden path

Let $h$ be a hidden Markov model with state set $S$, observation set $O$ and real weights: initial weights $\pi(s)$, transition weights $a(s, s')$ and emission weights $b(s, o)$. For $t \in \mathbb{N}$, a path $z = (z_0, \dots, z_t)$ and an observation string $x = (x_0, \dots, x_t)$, the observation weight is

$$w(x \mid z) = \prod_{i=0}^{t} b(z_i, x_i) \in \mathbb{R}.$$
