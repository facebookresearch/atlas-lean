# Face numbers of the cyclic polytope

For natural numbers $n$, $d$ and $k$, the value is

$$
\sum_{j=0}^{k+1} \binom{d-j}{k+1-j} \binom{n-d-1+m_j}{m_j}, \qquad m_j = \min(j, d-j),
$$

where subtraction is truncated at $0$. The second binomial coefficient is the cyclic polytope
h-vector entry $h_j$, so for $k < d$ and $n \ge d + 1$ this sum is the inverse h-to-f transform
of the h-vector of the cyclic polytope $C(n, d)$, that is, the number of $k$-dimensional faces
of $C(n, d)$.
