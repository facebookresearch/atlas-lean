# Number of adjacent pairs that are not an increase by one

For a list of integers $\ell = (\ell_0, \dots, \ell_{L-1})$, the directed gap count
$\vec g(\ell)$ is the number of positions $k$ with $0 \le k \le L - 2$ and
$\ell_{k+1} - \ell_k \ne 1$: the number of adjacent pairs that are not an increase by exactly
one. A list with at most one entry has directed gap count $0$. Applied to a list framed by $0$
and $n + 1$, it gives the [signed breakpoint count](sbreaks.md) (Shamir and Peer, Lecture 11,
signed setting).
