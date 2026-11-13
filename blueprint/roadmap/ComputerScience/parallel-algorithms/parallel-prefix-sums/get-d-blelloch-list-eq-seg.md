# The list implementation computes the exclusive prefix products

Let $M$ be a monoid,
$k$ a natural number and $xs = (x_0, \dots, x_{2^k - 1})$ a list in $M$ of length $2^k$. For
every $j < 2^k$, the entry at position $j$ of Blelloch's list scan of $xs$ in $k$ rounds is
the exclusive prefix product $x_0 x_1 \cdots x_{j-1}$ (equal to $1$ when $j = 0$).
