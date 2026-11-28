# Boundary chain of a vertex list

For a finite list of points $(v_1, \dots, v_n)$ of the Euclidean plane $\mathbb{R}^2$, its cyclic edge list is $((v_1, v_2), (v_2, v_3), \dots, (v_{n-1}, v_n), (v_n, v_1))$ (empty for the empty list, and $((v_1, v_1))$ for a one-point list). The boundary chain of the list is the set of points of $\mathbb{R}^2$ lying on some closed segment $[u, w]$ with $(u, w)$ in the cyclic edge list:

$$\partial(v_1, \dots, v_n) = \bigcup_{(u, w)} [u, w] .$$
