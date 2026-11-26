# One-step expectation under the Moran process

For every real $r$, every natural number $N$, every state $i \in \{0, \dots, N\}$ and every real function $f$ on the natural numbers,

$$\sum_{j=0}^{N} P(i, j)\, f(j) = a_i\, f(i + 1) + b_i\, f(i - 1) + (1 - a_i - b_i)\, f(i),$$

where $P$ are the [one-step transition probabilities](moran-prob.md) and $i - 1$ is read as $0$ when $i = 0$. The boundary terms vanish, since $b_0 = 0$ and $a_N = 0$. For $r > 0$ the left side is the expectation of $f$ after one step of the Moran process started from $i$.
