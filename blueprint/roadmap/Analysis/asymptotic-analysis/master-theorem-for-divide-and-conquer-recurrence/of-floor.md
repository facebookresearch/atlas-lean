# Divide-and-conquer recurrences with floor division

Let $a > 0$, $b > 1$, $n_0 \ge 1$, and let $g$ be nonnegative on $[0, \infty)$ with $g(x) = \Theta(x^c)$. If $T : \mathbb{N} \to \mathbb{R}$ is positive for $n < n_0$ and satisfies $T(n) = a\,T(\lfloor n/b \rfloor) + g(n)$ for $n \ge n_0$, then $T$ satisfies the one-branch Akra–Bazzi recurrence with coefficient $a$, ratio $1/b$ and $r(n) = \lfloor n/b \rfloor$, so the master theorem applies to it.
