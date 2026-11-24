# Last-to-root move in a $d$-ary heap is ready for sift-down

Let $d$ be a natural number,
let $a$ be a $d$-ary heap ordered array with at least two entries over a linearly ordered type,
and let $b = (b_0, \dots, b_{m-1})$ be the array obtained from $a$ by the last-to-root move.
Then $b$ is ready for a $d$-ary sift-down at index $0$: $d \ge 2$, $0 < m$, and
$b_{\lfloor (j-1)/d \rfloor} \le b_j$ for every index $j$ with $0 < j < m$ whose parent index
$\lfloor (j-1)/d \rfloor$ is not $0$.
