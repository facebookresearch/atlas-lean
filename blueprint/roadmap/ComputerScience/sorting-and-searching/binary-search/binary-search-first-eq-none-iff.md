# Binary search reports absence exactly when the key is absent

Let
$a = (a_0, \dots, a_{n-1})$ be an array over a linearly ordered type, sorted in nondecreasing
order, and let $k$ be a key. Binary search for the first occurrence of $k$ in $a$ returns no index
if and only if $a_i \ne k$ for every $i < n$.
