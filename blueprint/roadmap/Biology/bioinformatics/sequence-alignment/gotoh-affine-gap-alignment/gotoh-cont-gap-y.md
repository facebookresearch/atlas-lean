# Gotoh continuation value after a gap in the first sequence

The value $Y(x, y) = G_{|x| + |y|}(x, y, Y)$, where $G$ is the [fuel-bounded recursion](gotoh-aux.md): the best affine score of an alignment of $x$ and $y$ given that the previous column was a gap in the first sequence. The first column is unrestricted; the previous state only makes a following gap in the first sequence cost $e$ instead of $o$.
