# The matrix $\tilde R_\alpha(n)$

For a sequence $\alpha = (\alpha_0, \alpha_1, \dots)$ of
rationals and a natural number $n$, $\tilde R_\alpha(n)$ is the $n \times n$ rational matrix
whose $(i, j)$ entry, for $1 \le i, j \le n$, is $(j-1)^{\underline{i-1}} / \Omega(\alpha, j)$
if $i \le j$ and $0$ if $i > j$, where
$\Omega(\alpha, j) = \sum_{l=0}^{j-1} (j-1)^{\underline{l}} \, \alpha_l$,
$m^{\underline{l}} = m(m-1)\cdots(m-l+1)$ is the falling factorial, and division by $0$ gives
$0$.
