# Number of new vertices when a cell is added

For Boolean values $e, w, n, s, ne, nw, se, sw$, read as indicators in $\{0, 1\}$ of the presence of the eight neighbouring cells of a new cell, the integer

$$\Delta V = \mathbf{1}[w + s + sw = 0] + \mathbf{1}[e + se + s = 0] + \mathbf{1}[n + nw + w = 0] + \mathbf{1}[ne + n + e = 0],$$

the number of corners of the new cell (bottom left, bottom right, top left, top right) not shared with any present neighbour.
