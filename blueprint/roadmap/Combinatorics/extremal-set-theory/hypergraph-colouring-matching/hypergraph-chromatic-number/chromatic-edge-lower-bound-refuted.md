# Alon's refutation of Erdős Problem 832

There is an integer $r \ge 3$ such that for
infinitely many $k$ there are an $n$ and an $r$-uniform hypergraph $H$ on the vertex set
$\{0, \dots, n-1\}$ with chromatic number $k$ (it is $k$-colorable but not $(k-1)$-colorable)
that either has fewer than $\binom{(r-1)(k-1)+1}{r}$ edges, or has exactly that many edges but is
not the complete $r$-uniform hypergraph on any set of $(r-1)(k-1)+1$ of its vertices.

Alon deduced this from an upper bound through Turán numbers: for an absolute constant $C$, every
$r \ge C$ and every $k \ge Cr$, some $r$-uniform hypergraph with chromatic number at least $k$ has
at most $(7/8)^r \binom{(r-1)(k-1)+1}{r}$ edges, and an edge-minimal one among these has
chromatic number exactly $k$. Known Turán bounds disprove the conjecture for every $r \ge 4$; the
case $r = 3$ is open.

## Sources

- T. F. Bloom, Erdős Problems, Problem #832, https://www.erdosproblems.com/832 (status DISPROVED); resolution: N. Alon, Hypergraphs with high chromatic number, Graphs Combin. 1 (1985), 387-389, with f(k, s) the least number of edges of a k-uniform hypergraph of chromatic number at least s: 'Erdős and Hajnal conjectured that for every fixed k, if s > s_0(k) then equality holds in (2)' (f(k, s) = C((s - 1)(k - 1) + 1, k)), and 'This conjecture is false, as easily follows from' Proposition 1 (an upper bound for f(k, s) through Turán numbers); erdosproblems.com/832: for an absolute C, r ≥ C and k ≥ C r there is an r-uniform hypergraph with chromatic number at least k and at most (7/8)^r C((r - 1)(k - 1) + 1, r) edges, known Turán bounds disprove the conjecture for every r ≥ 4, and r = 3 remains open, https://web.math.princeton.edu/~nalon/PDFS/Publications/Hypergraphs%20with%20high%20chromatic%20number.pdf.
