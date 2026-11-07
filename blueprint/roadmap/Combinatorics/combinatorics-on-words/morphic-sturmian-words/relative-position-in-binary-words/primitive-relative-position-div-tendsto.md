# Relative position asymptotic to $n$ and the golden ratio

Let $\varrho$ be a substitution
on the letters $a, b$ with substitution matrix $M$, where $M_{11} = |\varrho(a)|_a$,
$M_{12} = |\varrho(b)|_a$, $M_{21} = |\varrho(a)|_b$ and $M_{22} = |\varrho(b)|_b$ ($|v|_x$ is
the number of letters $x$ in $v$), and suppose $\varrho$ is primitive (some power of $M$ has all
entries positive). Let $w$ be a one-sided fixed point of $\varrho$ (so $\varrho(w) = w$) in which
both letters occur infinitely often, let $p_a(n)$ and $p_b(n)$ be the positions of the $n$-th $a$
and the $n$-th $b$ in $w$, and let $r(n) = p_b(n) - p_a(n)$. Then $r(n)/n \to 1$ as
$n \to \infty$ if and only if $(\varphi, 1)^T$ is an eigenvector of $M$, where
$\varphi = (1 + \sqrt 5)/2$ is the golden ratio.

Since $(\varphi, 1)^T$ is positive, this is the same as being a right Perron–Frobenius
eigenvector of $M$.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 41 (`jis-2025-25.1.5-lem-41`).
