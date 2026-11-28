# An eventually recurrent Laurent series times its annihilator

Let $h : \mathbb{Z} \to \mathbb{C}$, let $q = \sum_{i \le d} q_i X^i$ be a complex polynomial with coefficients $q_0, \dots, q_d$ for some $d \in \mathbb{N}$ (any bound on the degree; the zero polynomial is allowed), and let $N, T \in \mathbb{Z}$. Suppose $h(t) = 0$ for every $t < N$ and $\sum_{i=0}^{d} q_i\, h(t - i) = 0$ for every $t \ge T$. Then for every $X \ne 0$ at which $\sum_{t \in \mathbb{Z}} h(t) X^t$ is summable,

$$\Bigl(\sum_{t \in \mathbb{Z}} h(t)\, X^t\Bigr)\, q(X) = X^N \sum_{0 \le j < \max(T - N, 0)} \Bigl(\sum_{i=0}^{d} q_i\, h(N + j - i)\Bigr) X^j.$$

No condition $q(X) \ne 0$ is needed, nor any ordering of $N$ and $T$, and the polynomial on the right and the shift $N$ do not depend on $X$.
