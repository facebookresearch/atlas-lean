# Flatten

Let `m` be an index type. Let `n` be an index type. Let `i` be an index type. Let `j` be an index
type. Let `A` be a coefficient type. For `M : CStarMatrix m n (CStarMatrix i j A)`. The map flattens
a matrix of rectangular matrices by pairing its outer and inner row indices, and likewise its outer
and inner column indices.
