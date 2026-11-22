# Naive string matcher

Let $p = p_0 \cdots p_{m-1}$ be a pattern and
$t = t_0 \cdots t_{n-1}$ a text over an alphabet with a Boolean equality test. If $m \le n$, the
naive matcher handles the shifts $s = 0, 1, \dots, n - m$ in turn: it compares $p_i$ with
$t_{s+i}$ for $i = 0, 1, \dots$ until a comparison fails or all $m$ symbols are compared, and it
reports $s$ if no comparison failed. It returns the reported shifts in the order found, with cost
the total number of symbol comparisons executed, failed comparisons included. If $m > n$, it
reports no shift at cost $0$.
