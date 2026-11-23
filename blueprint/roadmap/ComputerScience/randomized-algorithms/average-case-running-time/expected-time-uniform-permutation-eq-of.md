# Constant running time on all rearrangements gives that expected time

Let $A$ be an
algorithm on lists whose running time $T_A(y)$ on each list $y$ is a natural number, let
$x = (x_0, \dots, x_{n-1})$ be a list of length $n$, and let $c$ be a natural number. If
$T_A(x_{\sigma(0)}, \dots, x_{\sigma(n-1)}) = c$ for every permutation $\sigma$ of
$\{0, \dots, n-1\}$, then the expected running time of $A$ when its input is $x$ rearranged by a
uniformly random permutation equals $c$.
