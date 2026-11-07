# Primitive substitutions with asymptotically linear relative position

Let $\varrho$ be a
substitution on the letters $a, b$ with substitution matrix $M$, where $M_{11} = |\varrho(a)|_a$,
$M_{12} = |\varrho(b)|_a$, $M_{21} = |\varrho(a)|_b$ and $M_{22} = |\varrho(b)|_b$ ($|v|_x$ is
the number of letters $x$ in $v$). Suppose $\varrho$ is primitive (some power of $M$ has all
entries positive), and let $w$ be a one-sided fixed point of $\varrho$ (so $\varrho(w) = w$) in
which both letters occur infinitely often. Let $p_a(n)$ and $p_b(n)$ be the positions of the
$n$-th $a$ and the $n$-th $b$ in $w$, let $r(n) = p_b(n) - p_a(n)$, let $k \ge 1$ be a natural
number and let $\tau = (k + \sqrt{k^2 + 4})/2$. With all limits taken as $n \to \infty$:
(a) the following are equivalent: $r(n)/n \to k$; $(\tau, 1)^T$ is an eigenvector of $M$;
$M$ has rows $(km + t, m)$ and $(m, t)$ for some natural numbers $m \ge 1$ and $t \ge 0$.
(b) the following are equivalent: $r(n)/n \to -k$; $(1, \tau)^T$ is an eigenvector of $M$;
$M$ has rows $(t, m)$ and $(m, km + t)$ for some natural numbers $m \ge 1$ and $t \ge 0$.
(c) the following are equivalent: $r(n)/n \to 0$; $(1, 1)^T$ is an eigenvector of $M$;
$M_{11} + M_{12} = M_{21} + M_{22}$.

These vectors are positive, so being an eigenvector of the primitive matrix $M$ is the same as
being its right Perron–Frobenius eigenvector.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 67 (`jis-2025-25.1.5-thm-67`).
