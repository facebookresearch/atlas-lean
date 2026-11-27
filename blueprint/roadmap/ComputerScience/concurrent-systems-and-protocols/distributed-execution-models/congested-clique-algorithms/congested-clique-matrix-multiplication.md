# Matrix multiplication in O(n^(1 - 2/omega + eta)) rounds of the congested clique

Let $\omega$ be the exponent of matrix multiplication. Over any ring, if processor $i$ holds row $i$ of two $n \times n$ matrices $S$ and $T$ with entries of $O(\log n)$ bits, the product $ST$ (row $i$ delivered to processor $i$) can be computed in $O(n^{1 - 2/\omega + \eta})$ rounds of the congested clique for every fixed $\eta > 0$, the constant depending on $\eta$ (the exponent $\omega$ is an infimum that need not be attained); with $\omega < 2.3729$ this is $O(n^{0.158})$; over semirings (such as the min-plus semiring) the bound is $O(n^{1/3})$ rounds. Consequences include triangle counting and $4$-cycle counting in directed and undirected graphs in $O(n^{0.158})$ rounds, and exact all-pairs shortest paths in unweighted undirected graphs in $\tilde O(n^{0.158})$ rounds.

## Proof sketch

Fix $\eta > 0$ and a bilinear algorithm multiplying $q \times q$ matrices with $q^{\sigma}$ products, where $\sigma < \omega + \eta'$ for a suitable $\eta' > 0$ depending on $\eta$. Simulate it in parallel: the recursion is split into $n$ groups of subproblems whose inputs are distributed so that each processor receives and sends $O(n^{2 - 2/\sigma})$ words; Lenzen routing delivers them in $O(n^{1 - 2/\sigma}) = O(n^{1 - 2/\omega + \eta})$ rounds. Over semirings, the three-dimensional block decomposition into $n^{1/3} \times n^{1/3} \times n^{1/3}$ blocks gives $O(n^{1/3})$ rounds.

## Depends on

- [The congested clique model](the-congested-clique-model.md)
- [Matrix multiplication exponent](../../../../TheoryOfComputation/algebraic-complexity/matrix-multiplication-exponent/matrix-multiplication-exponent.md)

## Proof depends on

- [Lenzen's deterministic constant-round routing and sorting in the congested clique](congested-clique-constant-round-routing.md)

## Sources

- K. Censor-Hillel, P. Kaski, J. H. Korhonen, C. Lenzen, A. Paz, J. Suomela, "Algebraic Methods in the Congested Clique", PODC 2015; Distributed Computing 32 (2019), arXiv:1503.04963, Theorem 1 and Corollaries 2 and 7.
