# New vertices of an added cell match the local count

Let $S \subseteq \mathbb{Z}^2$ be a finite set of unit cells (labelled by lower left corners) and $(x, y) \notin S$ a cell. Write $e, w, n, s, ne, nw, se, sw \in \{0, 1\}$ for the indicators that the cells $(x+1, y)$, $(x-1, y)$, $(x, y+1)$, $(x, y-1)$, $(x+1, y+1)$, $(x-1, y+1)$, $(x+1, y-1)$, $(x-1, y-1)$ belong to $S$. Then the number of corners of $(x, y)$ that are not corners of any cell of $S$ equals

$$\mathbf{1}[w + s + sw = 0] + \mathbf{1}[e + se + s = 0] + \mathbf{1}[n + nw + w = 0] + \mathbf{1}[ne + n + e = 0].$$
