# First element at or above a uniquely attained height

Let $f$ map a type to a linearly
ordered set, let $y$ be a value, and let $T$ be a list sorted non-strictly by $f$, that is,
$f(j) \le f(k)$ whenever $j$ occurs before $k$ in $T$. Suppose $b$ lies in $T$ with $f(b) = y$,
and every element $c \ne b$ of $T$ has $f(c) \ne y$. Then removing from $T$ its longest prefix of
elements $j$ with $f(j) < y$ leaves a list whose first element is $b$.
