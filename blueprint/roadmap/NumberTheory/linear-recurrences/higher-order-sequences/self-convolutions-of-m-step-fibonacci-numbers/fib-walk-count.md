# Fibonacci self-convolution

For $n \ge 0$, $v_n$ is the rational number
$v_n = \sum_{j=0}^{n} F_{j+1} F_{n-j+1}$, where $F_i$ is the $i$-th Fibonacci number
($F_0 = 0$, $F_1 = 1$).

In the source, $v_n$ counts the shortest walks with a single upward step, taken along a vertical
tile boundary, over all tilings of a $1 \times n$ board by monominoes and dominoes.
