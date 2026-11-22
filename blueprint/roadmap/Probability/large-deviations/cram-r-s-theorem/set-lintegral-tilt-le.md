# Tilted Chernoff bound for a half-space event

Let $\mu$ be a probability measure and let $X_0, X_1, \dots$ be measurable, independent random
vectors in $\mathbb{R}^d$, each identically distributed with $X_0$, with
$\mathbb{E}[e^{\langle t, X_0\rangle}] < \infty$ for every $t$; put $S_n = \sum_{i < n} X_i$ and
$\Lambda(t) = \log \mathbb{E}[e^{\langle t, X_0\rangle}]$. Let $\theta, e \in \mathbb{R}^d$,
$c \in \mathbb{R}$, $s \ge 0$ and $n > 0$, and let $W_n = \exp(\langle \theta, S_n\rangle - n \Lambda(\theta))$. Then

$$\int_{\{n c \le \langle e, S_n\rangle\}} W_n \, d\mu \le \exp\big(n\,(\Lambda(\theta + s e) - \Lambda(\theta) - s c)\big).$$
