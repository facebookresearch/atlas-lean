# Longest common subsequence by dynamic programming

Given lists $x = x_1 \cdots x_m$ and
$y = y_1 \cdots y_n$ over a type with a boolean equality test, fill a table $c_{i,j}$ for
$0 \le i \le m$ and $0 \le j \le n$ by $c_{i,0} = c_{0,j} = 0$, by $c_{i,j} = c_{i-1,j-1} + 1$ when
the test reports $x_i = y_j$, and by $c_{i,j} = \max(c_{i-1,j}, c_{i,j-1})$ otherwise. Then build
a witness $w$ by walking back from $(m, n)$ until $i = 0$ or $j = 0$: when the test reports
$x_i = y_j$, put $x_i$ in front of $w$ and move to $(i-1, j-1)$; otherwise move to $(i-1, j)$ if
$c_{i-1,j} \ge c_{i,j-1}$ and to $(i, j-1)$ if not. The algorithm returns the pair $(c_{m,n}, w)$.

The abstract time counts one step for each table entry $c_{i,j}$ with $i, j \ge 1$ and one for
each backward step taken from a position with $i, j \ge 1$; everything else is free.
