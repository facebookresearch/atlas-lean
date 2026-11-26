# Matrix multiplication in O(n^(1 - 2/omega)) rounds of the congested clique

Let $\omega$ be the exponent of matrix multiplication. Over any ring, if processor $i$ holds row $i$ of two $n \times n$ matrices $S$ and $T$ with entries of $O(\log n)$ bits, the product $ST$ (row $i$ delivered to processor $i$) can be computed in $O(n^{1 - 2/\omega})$ rounds of the congested clique, which is $O(n^{0.158})$ with $\omega < 2.3729$; over semirings (such as the min-plus semiring) the bound is $O(n^{1/3})$ rounds. Consequences include triangle counting and $4$-cycle counting in $O(n^{0.158})$ rounds, and exact unweighted all-pairs shortest paths in $\tilde O(n^{0.158})$ rounds.

## Proof sketch

Simulate a parallel bilinear algorithm: a fast matrix multiplication with $n^{\omega}$ arithmetic products is recursively split into $n$ groups of subproblems whose inputs, of total size about $n^{2 - 2/\omega} \cdot n$ words, are distributed so that each processor receives and sends $O(n^{2 - 2/\omega})$ words; Lenzen routing delivers them in $O(n^{1 - 2/\omega})$ rounds. Over semirings, the three-dimensional block decomposition into $n^{1/3} \times n^{1/3} \times n^{1/3}$ blocks gives $O(n^{1/3})$ rounds.

## Depends on

- [The congested clique model](the-congested-clique-model.md)
- [Matrix multiplication exponent](../../../../TheoryOfComputation/algebraic-complexity/matrix-multiplication-exponent/matrix-multiplication-exponent.md)

## Proof depends on

- [Lenzen's deterministic constant-round routing and sorting in the congested clique](congested-clique-constant-round-routing.md)

## Sources

- K. Censor-Hillel, P. Kaski, J. H. Korhonen, C. Lenzen, A. Paz, J. Suomela, "Algebraic Methods in the Congested Clique", PODC 2015; Distributed Computing 32 (2019), arXiv:1503.04963.
