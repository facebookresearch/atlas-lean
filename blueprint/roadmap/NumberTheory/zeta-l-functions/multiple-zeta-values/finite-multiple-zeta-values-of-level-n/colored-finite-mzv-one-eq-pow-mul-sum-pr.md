# Decomposition of finite multiple zeta values into level-$N$ pieces

Let $N \ge 1$ and
let $k = (k_1, \dots, k_r)$ be a finite sequence of natural numbers (entries equal to $0$ are
allowed) of weight $w = k_1 + \dots + k_r$. For a prime $p$ put
$\zeta_p(k) = \sum_{0 < m_1 < \dots < m_r < p} m_1^{-k_1} \cdots m_r^{-k_r}$ in
$\mathbb{Z}/p\mathbb{Z}$, and for $0 \le j < N$ and a finite sequence $l$ let
$\zeta^{[j]}_{p,N}(l)$ be the colored finite multiple harmonic sum of level $N$ of $l$ with every
color equal to the class of $-jp$ modulo $N$. Then for all sufficiently large primes $p$

$$
\zeta_p(k) = N^w \sum_{0 \le i_1 \le \dots \le i_{N-1} \le r} \prod_{j=0}^{N-1}
\zeta^{[j]}_{p,N}(k_{i_j + 1}, \dots, k_{i_{j+1}}),
$$

where $i_0 = 0$, $i_N = r$, and $(k_{i_j + 1}, \dots, k_{i_{j+1}})$ is empty when
$i_j = i_{j+1}$.

## Sources

- Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of Level N*, INTEGERS 24 (2024), Article A22, Proposition 1 (`integers-2024-A22-prop-1`).
