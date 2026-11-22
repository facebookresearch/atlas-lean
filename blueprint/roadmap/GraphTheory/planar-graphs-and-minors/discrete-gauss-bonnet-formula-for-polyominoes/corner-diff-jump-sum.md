# Change of the corner defect in terms of eight neighbours

Let $S$ be a finite set of unit cells (labelled by lower left corners) and $(x, y) \notin S$ a cell. Write $e, w, n, s, ne, nw, se, sw \in \{0, 1\}$ for the indicators that the cells $(x+1, y)$, $(x-1, y)$, $(x, y+1)$, $(x, y-1)$, $(x+1, y+1)$, $(x-1, y+1)$, $(x+1, y-1)$, $(x-1, y-1)$ belong to $S$. Let $n_S(v)$ be the number of cells of $S$ with corner $v$, $\omega(k) = \mathbf{1}[k = 1] - \mathbf{1}[k = 3]$ and $J(m) = \omega(m+1) - \omega(m)$. Then

$$\sum_{v \text{ corner of } (x, y)} \Big(\omega\big(n_S(v) + 1\big) - \omega\big(n_S(v)\big)\Big) = J(w + s + sw) + J(e + se + s) + J(n + nw + w) + J(ne + n + e).$$
