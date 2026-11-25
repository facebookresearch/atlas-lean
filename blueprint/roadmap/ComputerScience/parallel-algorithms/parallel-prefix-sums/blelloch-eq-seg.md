# Blelloch's scan computes the exclusive prefix products

Let $M$ be a monoid, $k$ a
natural number and $x = (x_0, x_1, \dots)$ a sequence in $M$. For every $j < 2^k$, the value at
position $j$ of Blelloch's scan of $x$ on $2^k$ positions is the exclusive prefix product
$x_0 x_1 \cdots x_{j-1}$ (equal to $1$ when $j = 0$).
