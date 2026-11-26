# Polygonal partial-sum process

Let $X_0, X_1, \dots$ be real-valued functions on a set
$\Omega$. For $n \in \mathbb{N}$ and $\omega \in \Omega$, $S_n(\omega)$ is the element of the space
$C([0,1], \mathbb{R})$ of continuous real functions on $[0,1]$ defined by $S_0(\omega) = 0$ and,
for $n \ge 1$ and $t \in [0,1]$,

$$S_n(\omega)(t) = \frac{1}{\sqrt{n}} \sum_{i=0}^{n-1} X_i(\omega) \min(\max(nt - i, 0), 1).$$

Thus for $n \ge 1$, $S_n(\omega)$ linearly interpolates the values
$(X_0(\omega) + \dots + X_{k-1}(\omega))/\sqrt{n}$ at the times $k/n$ for $0 \le k \le n$.
