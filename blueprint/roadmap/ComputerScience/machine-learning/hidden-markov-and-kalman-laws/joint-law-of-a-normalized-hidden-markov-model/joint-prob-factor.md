# Joint weight of a hidden Markov model factors into prior and emission weights

Let $h$ be a hidden Markov model with finite state set $S$, finite observation set $O$ and real weights: initial weights $\pi(s)$, transition weights $a(s, s')$ and emission weights $b(s, o)$. For every $t \in \mathbb{N}$, path $z = (z_0, \dots, z_t)$ and observation string $x = (x_0, \dots, x_t)$, the joint weight factors as

$$P(z, x) = \Big(\pi(z_0) \prod_{i=0}^{t-1} a(z_i, z_{i+1})\Big) \cdot \prod_{i=0}^{t} b(z_i, x_i) .$$

No positivity or normalization is assumed; zero entries make both sides zero.
