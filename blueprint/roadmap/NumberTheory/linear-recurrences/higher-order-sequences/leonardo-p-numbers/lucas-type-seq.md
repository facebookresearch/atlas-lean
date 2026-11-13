# Lucas-type recurrence lists

Let $\alpha$ be a type with a zero, a one and an addition, let
$p$ be a natural number and let $a_0, c \in \alpha$. Define $a_i = 1$ for $1 \le i \le p$ and
$a_n = a_{n-1} + a_{n-p-1} + c$ for $n > p$. For every natural number $n$, the Lucas-type list
with parameters $p$, $a_0$, $c$ ending at index $n$ is $[a_0, a_1, \dots, a_n]$.

The list is built by appending one value per step, so each earlier value is computed once and
evaluation is quadratic in $n$, not exponential as with the naive two-branch recursion. The
Lucas and Lucas-Leonardo $p$-numbers are the cases $c = 0$ and $c = p$.

## Sources

- Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Section 1, display (5).
