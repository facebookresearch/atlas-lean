# Bracketing numbers of halfspaces and embeddable classes

For $\epsilon > 0$ and a measure $\mu$, an $\epsilon$-bracket for binary functions is a pair $\ell \le u$ (pointwise) with $\Pr_{x\sim\mu}[\ell(x) \ne u(x)] \le \epsilon$, covering every $g$ with $\ell \le g \le u$, and the bracketing number $N_{[\,]}(G, \mu, \epsilon)$ is the least number of $\epsilon$-brackets covering every $g \in G$. Then: the class of halfspaces in $\mathbb{R}^d$ satisfies $N_{[\,]}(H, \mu, \epsilon) \le (d/\epsilon)^{O(d)}$ for every measure $\mu$; every class embeddable as halfspaces in $m$ dimensions (via a feature map $\psi : X \to \mathbb{R}^m$) satisfies $N_{[\,]}(G, \nu, \epsilon) \le (m/\epsilon)^{O(m)}$ for every measure $\nu$; and intersections or unions of $k$ functions from classes $F_1, \dots, F_k$ satisfy $N_{[\,]}(F_1 \cdots F_k, \mu, k\epsilon) \le \prod_{i \le k} N_{[\,]}(F_i, \mu, \epsilon)$. Also, the class of symmetric differences $\{f \,\triangle\, f'\}$ satisfies $N_{[\,]}(G, \mu, 4\epsilon) \le N_{[\,]}(F, \mu, \epsilon)^4$. Consequently, for absolute constants $c_1, c_2$, polynomial threshold functions of degree $d$ in $\mathbb{R}^n$ satisfy $N_{[\,]} \le \exp(c_1 n^d \ln(n^d/\epsilon))$ and $k$-polytopes in $\mathbb{R}^n$ satisfy $N_{[\,]} \le \exp(c_2 nk\ln(nk/\epsilon))$, and the smoothed regret bound against adaptive adversaries gives regret $\tilde O(\sqrt{T\,\mathrm{VCdim}\,\ln(1/\sigma)})$ for these classes.

## Proof sketch

Halfspaces: discretize normal vectors and offsets so that the symmetric difference of nearby halfspaces has small $\mu$-mass, which needs a measure-adapted grid built from a VC-type argument (Braverman et al.); the bracket of a halfspace is the pair of the intersection and union of the halfspaces in a small neighbourhood. Embedding transports brackets through $\psi$ since $\psi$ pushes $\nu$ forward to a measure on $\mathbb{R}^m$. For intersections, intersect the lower and upper bracket functions coordinatewise; the gap of the intersection is at most the sum of the gaps.

## Depends on

- [Smoothed regret bounds depending on VC dimension and bracketing numbers](smoothed-online-regret-bounds.md)

## Sources

- N. Haghtalab, T. Roughgarden, A. Shetty, "Smoothed Analysis of Online and Differentially Private Learning", NeurIPS (2020), arXiv:2006.10129, Definition 2.1, Theorems 3.4, 3.6 and 3.7, Corollary 3.8.
