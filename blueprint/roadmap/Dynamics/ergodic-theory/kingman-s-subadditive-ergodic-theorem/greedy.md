# Greedy decomposition along an orbit

Let $T : \Omega \to \Omega$ be a map, $X_n : \Omega \to \mathbb{R}$ ($n \ge 0$) functions, $\varepsilon \ge 0$,
$N \ge 1$ and $\omega \in \Omega$; write $\omega_i = T^i \omega$. Let $g$ be the [real lower limit](g-low.md) of
$X_n/n$, $d$ the [per-step budget](dep.md) of $\varepsilon$ and $N$, and $R = \sum_{r<N} X_r^+$ the
[dominating function](rem-dom.md). Suppose that along the orbit of $\omega$:

- $X_{a+b}(\omega_s) \le X_a(\omega_s) + X_b(\omega_{s+a})$ for all $s, a, b \ge 0$;
- $g(\omega_i) \le g(\omega_j)$ whenever $i \le j$;
- $g(\omega_i) \ge 0$ and $X_1(\omega_i) \ge 0$ for every $i$;
- $X_n(\omega_i) \le R(\omega_i)$ for every $i$ and every $n < N$.

Then for all $n, s \ge 0$ there is $m$ with $m \le n \le m + N$ and

$$X_n(\omega_s) \le \sum_{j=0}^{n-1} d(\omega_{s+j}) + R(\omega_{s+m}).$$
