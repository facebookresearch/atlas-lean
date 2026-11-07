# Continued fraction convergents as matrix paths

Let
$R = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ and
$L = \begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}$, as matrices over $\mathbb{N}$. Let
$q_0, q_1, q_2, \dots$ be natural numbers, and define natural numbers $A_k$, $B_k$ for $k \ge -1$
by $A_{-1} = 1$, $A_0 = q_0$, $B_{-1} = 0$, $B_0 = 1$ and, for $k \ge 1$,
$A_k = q_k A_{k-1} + A_{k-2}$ and $B_k = q_k B_{k-1} + B_{k-2}$. For $n \ge 0$ let
$W_n = M_0^{q_0} M_1^{q_1} \cdots M_n^{q_n}$, where $M_i = R$ for even $i$ and $M_i = L$ for odd
$i$. Then $W_n = \begin{pmatrix} A_{n-1} & A_n \\ B_{n-1} & B_n \end{pmatrix}$ when $n$ is even,
and $W_n = \begin{pmatrix} A_n & A_{n-1} \\ B_n & B_{n-1} \end{pmatrix}$ when $n$ is odd.

When every $q_i$ is positive, $A_k / B_k$ is the $k$-th convergent of $[q_0; q_1, q_2, \dots]$,
and the parity of $n$ says whether the path $W_n$ ends with an $R$-move or an $L$-move, which is
the paper's case split; the identity holds for all $q_i \ge 0$.

## Sources

- Hongshen Chua, *Binary Trees and Sum of Two Squares*, INTEGERS 26 (2026), Article A76, Theorem 1 (`integers-2026-A76-thm-1`).
