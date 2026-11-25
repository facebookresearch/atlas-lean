# Cross-entropy

For probability mass functions $p$ and $q$ on a finite alphabet, the
cross-entropy of $q$ relative to $p$ is $H(p, q) = \sum_a p(a) \cdot (-\log_2 q(a))$ in bits, a
value in $[0, \infty]$. Here $-\log_2 q(a)$ is the surprisal of $a$ under $q$, which is $\infty$
when $q(a) = 0$, and a term with $p(a) = 0$ contributes $0$. So $H(p, q)$ is $\infty$ exactly
when $p$ charges an outcome that $q$ rules out.
