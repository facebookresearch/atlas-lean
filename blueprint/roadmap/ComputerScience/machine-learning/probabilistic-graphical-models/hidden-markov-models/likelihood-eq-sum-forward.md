# The forward algorithm computes the likelihood

Let $h$ be a hidden Markov model with a
finite set of states $S$, initial weights $\pi$, transition weights $a$ and emission weights $b$ in
a semiring, and let $x_0, x_1, \dots$ be observations. Let $\alpha$ be the forward variables,
$\alpha_0(s) = \pi(s)\, b(s, x_0)$ and
$\alpha_{t+1}(s) = \bigl(\sum_{s' \in S} \alpha_t(s')\, a(s', s)\bigr)\, b(s, x_{t+1})$. Then for
every $t \in \mathbb{N}$ the likelihood of $x_0, \dots, x_t$ equals $\sum_{s \in S} \alpha_t(s)$.
