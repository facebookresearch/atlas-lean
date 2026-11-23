# Number of adjacent pairs whose absolute difference is not one

For a list of integers $\ell = (\ell_0, \dots, \ell_{L-1})$, the gap count $g(\ell)$ is the
number of positions $k$ with $0 \le k \le L - 2$ and $|\ell_{k+1} - \ell_k| \ne 1$: the number
of adjacent pairs that are not consecutive integers, in either order. A list with at most one
entry has gap count $0$. Applied to a list framed by $0$ and $n + 1$, it gives the
[unsigned breakpoint count](ubreaks.md).
