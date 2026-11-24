# $\mathcal{M}_2$ as a coding of a uniform morphic word

Let $\sigma$ be the $4$-uniform
morphism on $\{0, 1, 2, 3\}$ with $\sigma(0) = 0132$, $\sigma(1) = 2310$, $\sigma(2) = 3201$ and
$\sigma(3) = 1023$. There is a sequence $w$ with values in $\{0, 1, 2, 3\}$ such that $w(0) = 0$,
$w(4n + r)$ is the letter of $\sigma(w(n))$ in position $r$ (counting from $0$) for all $n \ge 0$
and $0 \le r < 4$, and, for every $n$, the meta-automatic sequence $\mathcal{M}_2$ satisfies
$\mathcal{M}_2(n) = 1$ if $w(n)$ is odd and $\mathcal{M}_2(n) = 0$ if $w(n)$ is even. Thus
$w$ is the fixed point of $\sigma$ starting with $0$, and $\mathcal{M}_2$ is its image under the
coding $0, 2 \mapsto 0$ and $1, 3 \mapsto 1$.

## Sources

- John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.1, Corollary 23 (`jis-2026-26.4.1-cor-23`).
