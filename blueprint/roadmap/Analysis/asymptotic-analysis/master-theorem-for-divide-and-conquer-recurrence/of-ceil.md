# Divide-and-conquer recurrences with ceiling division

Let $a > 0$, $b > 1$, and $n_0 \ge 1$ with $b/(b-1) \le n_0$, and let $g$ be nonnegative on $[0, \infty)$ with $g(x) = \Theta(x^c)$. If $T : \mathbb{N} \to \mathbb{R}$ is positive for $n < n_0$ and satisfies $T(n) = a\,T(\lceil n/b \rceil) + g(n)$ for $n \ge n_0$, then $T$ satisfies the one-branch Akra–Bazzi recurrence with coefficient $a$, ratio $1/b$ and $r(n) = \lceil n/b \rceil$. The cutoff $b/(b-1) \le n_0$ is the sharp condition for $\lceil n/b \rceil < n$, also when $1 < b < 2$, and $a$ need not be at least one.
