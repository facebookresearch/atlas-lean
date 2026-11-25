# Normalized DCG lies in $[0, 1]$

Let $k \le N$, gains $g_1, \dots, g_N \ge 0$, discounts $w_1 \ge \dots \ge w_k \ge 0$, an ideal ranking that sorts all $N$ candidates by nonincreasing gain, and an injective ranked prefix $r$ of length $k$. Then the normalized DCG, $\sum_i w_i g_{r(i)}$ divided by the ideal DCG (and $0$ when the ideal DCG is $0$), lies in $[0, 1]$.
