# One-pass satisfy-count from a variable

For natural numbers $m$ and $n$ and a diagram $t$,
the satisfy-count $c_m(n, t)$ of $t$ from $n$ with bound $m$ is defined by recursion on $t$: a
leaf $\mathrm{true}$ gives $2^{m - n}$, a leaf $\mathrm{false}$ gives $0$, and a node testing the
variable $v$ with child $t_0$ for false and child $t_1$ for true gives
$2^{v - n} (c_m(v + 1, t_0) + c_m(v + 1, t_1))$. Here $m - n$ and $v - n$ are truncated
subtraction, equal to $0$ when the difference would be negative.

For $t$ ordered from $n$ whose tested variables are all below $m$, $c_m(n, t)$ is the number of
assignments to the variables $n, \dots, m - 1$ that make $t$ true.
