# $d$-ary heap order

Let $d$ be a natural number and $a = (a_0, \dots, a_{n-1})$ an array
with entries in a type carrying a relation $\le$. The array $a$ is $d$-ary heap ordered when
$d \ge 2$ and every nonroot entry is at least the entry at its parent index:
$a_{\lfloor (i-1)/d \rfloor} \le a_i$ for every index $i$ with $0 < i < n$.
