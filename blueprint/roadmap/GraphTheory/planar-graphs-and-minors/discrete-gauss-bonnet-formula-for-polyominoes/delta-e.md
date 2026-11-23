# Number of new edges when a cell is added

For Boolean values $e, w, n, s$, read as indicators $\mathbf{1}_e, \mathbf{1}_w, \mathbf{1}_n, \mathbf{1}_s \in \{0, 1\}$ of the presence of the east, west, north and south neighbours of a new cell, the integer

$$\Delta E = (1 - \mathbf{1}_s) + (1 - \mathbf{1}_n) + (1 - \mathbf{1}_w) + (1 - \mathbf{1}_e),$$

the number of sides of the new cell that are not shared with a present neighbour.
