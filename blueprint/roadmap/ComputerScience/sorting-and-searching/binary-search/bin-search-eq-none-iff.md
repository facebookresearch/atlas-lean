# Bounded binary search on a sorted array fails exactly when the key is absent

Let
$A = (a_0, \dots, a_{n-1})$ be an array of length $n$ with entries in a linearly ordered type,
with $a_i \le a_j$ whenever $i < j$. Let $k$ be an element of that type and $\ell$, $h$ natural
numbers. Lean core's array binary search for $k$ in $A$, with the strict order $<$ as comparison
and inclusive bounds $\ell$ and $h$, returns no element if and only if there is no index $i < n$
with $\ell \le i \le h$ and $a_i = k$.
