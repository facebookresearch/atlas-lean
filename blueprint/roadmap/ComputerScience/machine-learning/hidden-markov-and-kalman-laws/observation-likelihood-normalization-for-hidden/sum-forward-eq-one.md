# Forward variables of a normalized hidden Markov model sum to one

Let $h$ be a hidden Markov model with finite state set $S$, finite observation set $O$ and real weights: initial weights $\pi(s)$, transition weights $a(s, s')$ and emission weights $b(s, o)$. Assume $h$ is normalized: $\pi \ge 0$ with $\sum_s \pi(s) = 1$, $a \ge 0$ with $\sum_{s'} a(s, s') = 1$ for every $s$, and $b \ge 0$ with $\sum_o b(s, o) = 1$ for every $s$ (zero entries allowed). A finite observation string $v = (v_0, \dots, v_t)$ is extended to a stream by $\bar v_i = v_i$ for $i \le t$ and $\bar v_i = v_0$ for $i > t$. Let $\alpha_t(s)$ be the forward variables, $\alpha_0(s) = \pi(s)\, b(s, x_0)$ and $\alpha_{t+1}(s) = \big(\sum_{s'} \alpha_t(s')\, a(s', s)\big)\, b(s, x_{t+1})$, computed on the stream $x = \bar v$.

Then for every $t \in \mathbb{N}$,

$$\sum_{v \in O^{t+1}} \sum_{s \in S} \alpha_t(s) = 1 .$$
