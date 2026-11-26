# The maximal $L$-block $\theta^{m+1}$

Let $L = (e_1, \dots, e_N)$ be a list of natural
numbers and $m \in \mathbb N$, with indices of coefficient functions starting at $0$. The maximal
$L$-block $\theta^{m+1}$ is the finitely supported coefficient function whose entry at each index
$i < m$ is $e_j$, where $j - 1 = (m - 1 - i) \bmod N$, and whose entries at the indices $i \ge m$
are $0$ (every entry is $0$ when $L$ is empty).

In the paper's one-based indexing, $\theta^n = \mathrm{rev}_{n-1}(\beta^*)$, where $\beta^*$ is
the coefficient function with $\beta^*_k = e_j$ for $k \equiv j \pmod N$ and
$\mathrm{rev}_{n-1}(\beta^*)$ lists the first $n - 1$ entries of $\beta^*$ in reverse order,
followed by zeros.

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Definition 10 (arXiv:2308.12872v1, Section 2.2).
