# Letter frequencies and mean positions of primitive fixed points

Let $\varrho$ be a
substitution on the letters $a, b$ with substitution matrix $M$, where $M_{11} = |\varrho(a)|_a$,
$M_{12} = |\varrho(b)|_a$, $M_{21} = |\varrho(a)|_b$ and $M_{22} = |\varrho(b)|_b$ ($|v|_x$ is
the number of letters $x$ in $v$). Suppose $\varrho$ is primitive (some power of $M$ has all
entries positive), and let $u > 0$ and $\lambda$ be real numbers with
$M (u, 1)^T = \lambda (u, 1)^T$. Let $w$ be a one-sided fixed point of $\varrho$ (so
$\varrho(w) = w$) in which both letters occur infinitely often. Let $N_a(n)$ and $N_b(n)$ be the
numbers of letters $a$ and $b$ among the first $n$ letters of $w$, let $p_a(n)$ and $p_b(n)$ be
the positions of the $n$-th $a$ and the $n$-th $b$ in $w$, and let $r(n) = p_b(n) - p_a(n)$.
Then, as $n \to \infty$, $N_a(n)/n \to u/(u + 1)$, $N_b(n)/n \to 1/(u + 1)$,
$p_a(n)/n \to 1 + 1/u$, $p_b(n)/n \to u + 1$ and $r(n)/n \to u - 1/u$, and each of these five
limits lies in the subfield $\mathbb{Q}(\lambda)$ of $\mathbb{R}$.

A positive eigenvector of a primitive matrix belongs to its Perron–Frobenius eigenvalue, so
$(u, 1)^T$ is a right Perron–Frobenius eigenvector of $M$ and $\lambda$ is its eigenvalue.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 32 (`jis-2025-25.1.5-lem-32`).
