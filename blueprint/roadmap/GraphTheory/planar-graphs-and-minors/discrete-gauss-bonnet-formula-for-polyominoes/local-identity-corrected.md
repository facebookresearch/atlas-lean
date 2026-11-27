# Local cell Gauss–Bonnet identity

For all $e, w, n, s, ne, nw, se, sw \in \{0, 1\}$ (indicators of the eight neighbouring cells of a new cell), with $J(m) = w_c(m+1) - w_c(m)$, $w_c(k) = \mathbf{1}[k = 1] - \mathbf{1}[k = 3]$,

$$J(w + s + sw) + J(e + se + s) + J(n + nw + w) + J(ne + n + e) = 4\,(\Delta V - \Delta E + 1) + 2\,\Delta P,$$

where $\Delta V = \mathbf{1}[w + s + sw = 0] + \mathbf{1}[e + se + s = 0] + \mathbf{1}[n + nw + w = 0] + \mathbf{1}[ne + n + e = 0]$, $\Delta E = (1 - s) + (1 - n) + (1 - w) + (1 - e)$, and

$$\Delta P = \big(sw\,\bar w\,\bar s - w\,s\,\overline{sw}\big) + \big(se\,\bar e\,\bar s - e\,s\,\overline{se}\big) + \big(nw\,\bar n\,\bar w - n\,w\,\overline{nw}\big) + \big(ne\,\bar n\,\bar e - n\,e\,\overline{ne}\big)$$

with $\bar x = 1 - x$. That is, the change of the corner defect when a cell is added is four times the change of the Euler characteristic plus twice the change of the number of pinch points.
