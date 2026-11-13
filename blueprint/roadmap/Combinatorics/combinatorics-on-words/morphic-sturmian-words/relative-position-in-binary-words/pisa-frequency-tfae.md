# Frequency and position criteria for an eigenvector of a primitive substitution

Let
$j \ge 1$ and $m \ge 1$ be natural numbers with $m \ne j + 1$, and let
$\tau = (j + \sqrt{j^2 + 4m})/2$. Let
$\varrho$ be a substitution on the letters $a, b$ with substitution matrix $M$, where
$M_{11} = |\varrho(a)|_a$, $M_{12} = |\varrho(b)|_a$, $M_{21} = |\varrho(a)|_b$ and
$M_{22} = |\varrho(b)|_b$ ($|v|_x$ is the number of letters $x$ in $v$). Suppose $\varrho$ is
primitive (some power of $M$ has all entries positive), and let $w$ be a one-sided fixed point
of $\varrho$ (so $\varrho(w) = w$). Let $N_a(n)$ and $N_b(n)$ be the numbers of letters $a$ and
$b$ among the first $n$ letters of $w$, let $p_a(n)$ and $p_b(n)$ be the positions (counted from
$0$) of the $n$-th $a$ and the $n$-th $b$ in $w$, and let $r(n) = p_b(n) - p_a(n)$. Then the
following are equivalent, all limits taken as $n \to \infty$:
(i) $N_a(n)/n \to (\tau - m)/(j + 1 - m)$;
(ii) $N_b(n)/n \to (j + 1 - \tau)/(j + 1 - m)$;
(iii) $p_a(n)/n \to 1 + (\tau - j)/m$;
(iv) $p_b(n)/n \to \tau + 1$;
(v) $r(n)/n \to ((m - 1)\tau + j)/m$;
(vi) $p_a(n)/n$ converges to some real number $q$ and $r(n)/n \to (m - 1)q + j + 1 - m$;
(vii) $(\tau, 1)^T$ is an eigenvector of $M$.

The hypothesis $m \ne j + 1$ is added to the paper's statement: for $m = j + 1$ one has
$\tau = j + 1 = m$, so (i) and (ii) read $0/0$.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Proposition 62 (`jis-2025-25.1.5-prop-62`).
