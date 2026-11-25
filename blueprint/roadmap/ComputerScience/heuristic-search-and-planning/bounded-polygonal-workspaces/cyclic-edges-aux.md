# Closing a vertex list into directed edges

Given a point $f$ of the Euclidean plane $\mathbb{R}^2$ and a finite list of points, this list of directed edges links consecutive points and closes the last point back to $f$. It is defined recursively:

- the empty list gives no edges;
- a one-point list $(v)$ gives the single edge $(v, f)$;
- $(v_1, v_2, \dots)$ gives the edge $(v_1, v_2)$ followed by the edges of $(v_2, \dots)$ closed back to $f$.

So $(v_1, \dots, v_n)$ with $n \ge 1$ gives $((v_1, v_2), \dots, (v_{n-1}, v_n), (v_n, f))$.
