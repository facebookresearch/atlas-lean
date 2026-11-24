# Local change of the corner defect

For Boolean values $e, w, n, s, ne, nw, se, sw$, read as indicators in $\{0, 1\}$ of the presence of the eight neighbouring cells of a new cell, the integer

$$J(w + s + sw) + J(e + se + s) + J(n + nw + w) + J(ne + n + e),$$

where $J(m) = w_c(m+1) - w_c(m)$ with corner weight $w_c(k) = \mathbf{1}[k = 1] - \mathbf{1}[k = 3]$. It is the change of the corner defect at the four corners of the new cell.
