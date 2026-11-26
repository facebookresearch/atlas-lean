# Held–Karp algorithm

Let $d$ be a cost function on the cities with values in a linearly
ordered additive commutative monoid $R$, let $s$ be the start city and let `others` be a list of
distinct cities other than $s$. For $k = 1, 2, \dots$ up to the length of `others`, for each
sublist $A$ of `others` of length $k$ and each $v \in A$, the algorithm stores in a table, under
the set of cities of $A$ and $v$, the value $T(A, v) = d(s, v)$ if $A = [v]$, and otherwise the
minimum over the cities $u$ of $A$ other than $v$ of $T(A \setminus \{v\}, u) + d(u, v)$, read
from the table. It returns the minimum over the cities $v$ of `others` of
$T(\mathit{others}, v) + d(v, s)$, in $R \cup \{\top\}$. Its cost is a pair: the number of
steps, one for each base entry, one for each candidate $u$ examined in a minimum and one for each
closing candidate $v$; and the number of table entries stored.
