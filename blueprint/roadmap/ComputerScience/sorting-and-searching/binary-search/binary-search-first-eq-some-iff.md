# Binary search returns the first occurrence of the key

Let $a = (a_0, \dots, a_{n-1})$ be
an array over a linearly ordered type, sorted in nondecreasing order, let $k$ be a key and let $i$
be a natural number. Binary search for the first occurrence of $k$ in $a$ returns the index $i$ if
and only if $i < n$, $a_i = k$, and $a_j < k$ for every $j < i$.
