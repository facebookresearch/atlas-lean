# Powers of the Padovan–Perrin companion matrix

Let $R$ be a commutative ring, let
$k_1, k_2 \in R$, let $p, s$ be positive integers, and write $r = s + p$. Let $A$ be the
$r \times r$ matrix over $R$, with rows and columns indexed by $0, \dots, r - 1$, whose row $0$ has
$k_1$ in column $s - 1$, $k_2$ in column $r - 1$ and $0$ elsewhere, and whose entry in row
$a \ge 1$ and column $b$ is $1$ if $a = b + 1$ and $0$ otherwise. For $1 \le \ell \le r$ let
$v^{(\ell)}$ be the solution of the $([k]; p; s)$-Padovan–Perrin recurrence with
$v^{(\ell)}(m) = 1$ if $m + 1 = \ell$ and $v^{(\ell)}(m) = 0$ otherwise, for $0 \le m < r$. Then
for every $n \ge 0$ and all $0 \le i, j \le r - 1$,

$$(A^n)_{ij} = v^{(r - j)}(n + r - 1 - i).$$

## Sources

- Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino, *On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24 (2024), Article A49, Theorem 1, equations (5) and (9) (`integers-2024-A49-thm-1`).
