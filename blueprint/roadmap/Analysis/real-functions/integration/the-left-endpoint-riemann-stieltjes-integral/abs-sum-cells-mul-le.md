# Bound on weighted increments over the cells of a partition

Let $a \le b$, and let $V$ be a monotone control for $k$ on $[a, b]$: $|k(x) - k(y)| \le V(x) - V(y)$ whenever $a \le y \le x \le b$. Let $s$ be a finite set of reals, let the partition consist of $a$, $b$ and the points of $s$ strictly between them, and let $t : \mathbb{R} \to \mathbb{R}$ satisfy $|t(x)| \le M$ at every partition point $x$. Then

$$\Bigl|\sum_{x} t(x)\,\bigl(k(x) - k(x^-)\bigr)\Bigr| \le M\,\bigl(V(b) - V(a)\bigr),$$

the sum running over the partition points $x$, with $x^-$ the preceding partition point (and $a^- = a$). The order $a \le b$ matters: for $a = 1$, $b = 0$, $k(x) = V(x) = x$, $t = 1$ and $M = 1$, the control condition is vacuous, the partition is $\{0, 1\}$, the sum is $1$, and the right-hand side is $-1$.
