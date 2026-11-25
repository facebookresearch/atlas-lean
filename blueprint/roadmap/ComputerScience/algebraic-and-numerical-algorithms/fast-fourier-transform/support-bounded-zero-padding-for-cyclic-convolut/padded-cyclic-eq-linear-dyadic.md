# Dyadic zero padding turns cyclic convolution into linear convolution

For $x \in \mathbb{C}^M$ extend $x$ by zero to all natural indices, $\bar x_i = x_i$ for $i < M$ and $\bar x_i = 0$ otherwise. The linear convolution of $x \in \mathbb{C}^M$ and $y \in \mathbb{C}^K$ is $(x * y)_t = \sum_{j=0}^{t} \bar x_j\, \bar y_{t-j}$ for $t \in \mathbb{N}$. For $N \ge 1$ the zero extension of $x$ to $\mathbb{Z}/N$ is $x^{(N)}(i) = \bar x_{\tilde i}$, where $\tilde i \in \{0, \dots, N-1\}$ is the representative of $i$, and the cyclic convolution of $a, b : \mathbb{Z}/N \to \mathbb{C}$ is $(a \circledast b)(t) = \sum_{j \in \mathbb{Z}/N} a(j)\, b(t - j)$.

Let $d \in \mathbb{N}$, $n = 2^d$ and $x, y \in \mathbb{C}^{n}$. Then for every natural $t < 2n - 1$, with cyclic length $N = 2^{d+1}$,
$$\bigl(x^{(N)} \circledast y^{(N)}\bigr)(t \bmod N) = (x * y)_t.$$
