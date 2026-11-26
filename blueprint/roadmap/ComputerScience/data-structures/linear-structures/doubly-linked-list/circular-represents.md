# Circular doubly linked list with a sentinel

Let $S$ be a store of $n$ slots indexed by
$\{0, \dots, n-1\}$, each either empty or holding a node with a payload and optional next and
previous indices. The store $S$ represents a circular list with sentinel $s$ and data nodes
$x_1, \dots, x_k$ (a list of indices) when the $x_i$ are pairwise distinct and all differ from
$s$; slot $s$ holds a node whose next index is $x_1$ and whose previous index is $x_k$ (both
are $s$ when $k = 0$); and for every $i$ with $1 \le i \le k$, slot $x_i$ holds a node whose
previous index is $x_{i-1}$ and whose next index is $x_{i+1}$, where $x_0 = x_{k+1} = s$.
