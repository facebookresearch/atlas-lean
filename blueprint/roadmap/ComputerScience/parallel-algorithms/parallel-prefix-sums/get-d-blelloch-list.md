# Blelloch's list scan agrees with the scan of sequences

Let $M$ be a monoid, $k$ a natural
number and $xs = (x_0, \dots, x_{2^k - 1})$ a list in $M$ of length $2^k$. For every $j < 2^k$,
the entry at position $j$ of Blelloch's list scan of $xs$, with $k$ levels of recursion, equals the value at
position $j$ of Blelloch's scan on $2^k$ positions of the sequence
$x_0, \dots, x_{2^k - 1}, 1, 1, \dots$ obtained by extending $xs$ by $1$.
