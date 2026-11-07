# Support form of the IDP necessary condition

Let $r = (r_1, \dots, r_d)$ and
$x = (x_1, \dots, x_d)$ be tuples of natural numbers. The pair $(r, x)$ satisfies the support
form of the necessary condition when, for every index $j$,
$1 + \sum_{i=1}^{d} x_i (r_i \bmod r_j) = r_j$, where $r_i \bmod r_j$ is the remainder of $r_i$
on division by $r_j$, with the convention $r_i \bmod 0 = r_i$.

When every $x_i$ is positive, let $q$ be the weight vector in which each $r_i$ is repeated
$x_i$ times. Then this condition is equivalent to $1 + \sum_i (q_i \bmod q_j) = q_j$ for every
index $j$ of $q$.

## Sources

- Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60, Corollary 1.
