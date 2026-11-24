# The forward variables are path sums

Let $h$ be a hidden Markov model with a finite set of
states $S$ and weights in a semiring $R$, and let $x$ be an observation sequence. For every time
$t$ and every state $s$, the forward variable $\alpha_t(s)$ equals $\sum_z p_t(z)$, the sum
running over the state paths $z = (z_0, \dots, z_t) \in S^{t+1}$ with $z_t = s$, where $p_t(z)$
is the joint weight of $z$ and the observations $x_0, \dots, x_t$.
