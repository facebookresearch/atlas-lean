# Non-anti-recurrence numbers

Let $a = (a_1, \dots, a_k)$ be a linear form with natural
number coefficients. Its non-anti-recurrence numbers $B_1, B_2, \dots$ are produced in blocks of
$k$ by the mex rule: for $n \ge 1$, each of $B_{(n-1)k+1}, \dots, B_{nk}$ in turn is the least
positive integer not among $B_1, \dots, B_{(n-1)k}$, the anti-recurrence numbers
$A_1, \dots, A_{n-1}$ and the earlier entries of its block, and then
$A_n = a_1 B_{(n-1)k+1} + \dots + a_k B_{nk}$. For $k = 2$ the subsequences $B^1_n = B_{2n-1}$
and $B^2_n = B_{2n}$ are the paper's $B^1$ and $B^2$.

By Lemma 2 of the source, for a positive form with $k > 1$ the numbers $B_m$ are the positive
integers that are not anti-recurrence numbers, listed in increasing order.

## Sources

- Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026), Article A24, Section 2 (definition of anti-recurrence sequences).
