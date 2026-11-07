# Bounded binary search membership test on a sorted array is correct

Let
$A = (a_0, \dots, a_{n-1})$ be an array of length $n$ with entries in a linearly ordered type,
with $a_i \le a_j$ whenever $i < j$. Let $k$ be an element of that type and $\ell$, $h$ natural
numbers. Lean core's Boolean binary search membership test for $k$ in $A$, with the strict order
$<$ as comparison and inclusive bounds $\ell$ and $h$, returns true if and only if there is an
index $i < n$ with $\ell \le i \le h$ and $a_i = k$.
