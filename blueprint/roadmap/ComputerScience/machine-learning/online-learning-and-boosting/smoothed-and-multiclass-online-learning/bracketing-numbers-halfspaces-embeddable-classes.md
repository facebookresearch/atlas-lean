# Bracketing numbers of halfspaces and embeddable classes

For $\epsilon > 0$ and a measure $\mu$, an $\epsilon$-bracket is a pair of functions $\ell \le u$ with $\mathbb{E}_\mu[u - \ell] \le \epsilon$, and the bracketing number $N_{[\,]}(G, \mu, \epsilon)$ is the least number of $\epsilon$-brackets covering every $g \in G$. Then: the class of halfspaces in $\mathbb{R}^d$ satisfies $N_{[\,]}(H, \mu, \epsilon) \le (d/\epsilon)^{O(d)}$ for every measure $\mu$; every class embeddable as halfspaces in $m$ dimensions (via a feature map $\psi : X \to \mathbb{R}^m$) satisfies $N_{[\,]}(G, \nu, \epsilon) \le (m/\epsilon)^{O(m)}$ for every measure $\nu$; and intersections or unions of $k$ functions from classes $F_1, \dots, F_k$ satisfy $N_{[\,]}(F_1 \cdots F_k, \mu, k\epsilon) \le \prod_{i \le k} N_{[\,]}(F_i, \mu, \epsilon)$. Consequently polynomial threshold functions of degree $d$ in $\mathbb{R}^n$ and $k$-polytopes have bracketing numbers singly exponential in $n^d$ and in $nk$ respectively, and the smoothed regret bound applies to them.

## Proof sketch

Halfspaces: discretize normal vectors and offsets so that the symmetric difference of nearby halfspaces has small $\mu$-mass, which needs a measure-adapted grid built from a VC-type argument (Braverman et al.); the bracket of a halfspace is the pair of the intersection and union of the halfspaces in a small neighbourhood. Embedding transports brackets through $\psi$ since $\psi$ pushes $\nu$ forward to a measure on $\mathbb{R}^m$. For intersections, intersect the lower and upper bracket functions coordinatewise; the gap of the intersection is at most the sum of the gaps.

## Proof depends on

- [Smoothed regret bounds depending on VC dimension and bracketing numbers](smoothed-online-regret-bounds.md)

## Sources

- N. Haghtalab, T. Roughgarden, A. Shetty, "Smoothed Analysis of Online and Differentially Private Learning", NeurIPS (2020), arXiv:2006.10129.
