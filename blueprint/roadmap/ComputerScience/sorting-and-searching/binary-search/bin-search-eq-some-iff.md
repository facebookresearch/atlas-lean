# Result of bounded binary search on a sorted array

Let $A = (a_0, \dots, a_{n-1})$ be an
array of length $n$ with entries in a linearly ordered type, with $a_i \le a_j$ whenever $i < j$.
Let $k$ and $a$ be elements of that type and $\ell$, $h$ natural numbers. Lean core's array binary
search for $k$ in $A$, with the strict order $<$ as comparison and inclusive bounds $\ell$ and
$h$, returns $a$ if and only if $a = k$ and there is an index $i < n$ with $\ell \le i \le h$ and
$a_i = k$.

The requirement $i < n$ reflects the implementation's clamping of an upper bound $h \ge n$ to
$n - 1$.
