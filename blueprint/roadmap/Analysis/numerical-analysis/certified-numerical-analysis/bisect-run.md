# Bisection run

For a rational interval $I = [l, u]$ with midpoint $m$ and a finite list of Boolean decisions $d_1, \dots, d_n$, the bisection run applies the decisions in order: the decision true replaces $[l, u]$ by $[l, m]$ and the decision false replaces it by $[m, u]$. The empty list leaves $I$ unchanged.
