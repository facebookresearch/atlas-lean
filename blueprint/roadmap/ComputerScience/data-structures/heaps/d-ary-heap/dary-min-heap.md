# $d$-ary min-heap

A $d$-ary min-heap over a linearly ordered type $\alpha$ consists of a
natural number $d \ge 2$, its arity, and an array $a = (a_0, \dots, a_{n-1})$ of elements of
$\alpha$, stored in level order, that is $d$-ary heap ordered:
$a_{\lfloor (i-1)/d \rfloor} \le a_i$ for every index $i$ with $0 < i < n$.
