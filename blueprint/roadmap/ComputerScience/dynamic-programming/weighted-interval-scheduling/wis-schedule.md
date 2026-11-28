# Weighted interval scheduling algorithm

For intervals $1, \dots, n$ with start times $s$,
finish times $f$ and weights $w$, the algorithm sorts $1, \dots, n$ by finish time with merge sort
into the order $\sigma(1), \dots, \sigma(n)$ and stores that order in an array. For
$j = 1, \dots, n$ it finds $P_j$ by binary search: starting from $[lo, hi] = [0, j - 1]$, while
$lo < hi$ it compares $f(\sigma(m)) \le s(\sigma(j))$ at $m = \lfloor (lo + hi + 1)/2 \rfloor$ and
continues on $[m, hi]$ if this holds and on $[lo, m - 1]$ otherwise, and it takes $P_j = lo$. It
sets $M_0 = 0$ and $M_j = \max(M_{j-1}, w(\sigma(j)) + M_{P_j})$. It then traces back from $j = n$:
while $j \ge 1$, it takes $\sigma(j)$ and continues from $P_j$ if
$M_{j-1} < w(\sigma(j)) + M_{P_j}$, and continues from $j - 1$ otherwise. It returns $M_n$ and the
set of intervals taken. It charges one unit for each comparison of two finish times in the merge
sort, for each comparison $f(\sigma(m)) \le s(\sigma(j))$ in the binary searches, and for each
comparison of two weights in the table and the traceback; nothing else is charged.
