# Triangle detection in the congested clique in sublinear rounds

In the congested clique, a deterministic algorithm detects and lists all triangles of the input graph in $O(n^{1/3} / \log n)$ rounds; deciding whether a triangle exists can be done in $O(n^{1 - 2/\omega + \eta})$ rounds for every fixed $\eta > 0$, which is $O(n^{0.158})$ with $\omega < 2.3729$. Conversely, every triangle listing algorithm with error probability less than $1/32$ has expected round complexity $\Omega(n^{1/3}/\log n)$ on the random graph $G(n, 1/2)$, so listing is strictly harder than detection and counting in the congested clique.

## Proof sketch

Partition the vertex set into $n^{1/3}$ parts and assign each of the $n$ triples of parts to one processor, which must learn the $O(n^{4/3})$ edges between its three parts; each processor holds $O(n)$ edges and needs to send each to $O(n^{1/3})$ processors, so Lenzen-style routing finishes in $O(n^{1/3}/\log n)$ rounds after packing edges into messages. The listing lower bound is an information-theoretic argument on random inputs, not a count of the triangles of one fixed graph: on $G(n, 1/2)$ some processor outputs an expected $\Omega(n^2)$ triangles, since $t$ triangles span $\Omega(t^{2/3})$ edges, all of which the output reveals, the mutual information between the random edge set and that output is $\Omega(n^{4/3})$ bits, and this information must reach the processor through its transcript, at $O(n \log n)$ bits per round.

## Depends on

- [The congested clique model](the-congested-clique-model.md)
- [Matrix multiplication exponent](../../../../TheoryOfComputation/algebraic-complexity/matrix-multiplication-exponent/matrix-multiplication-exponent.md)

## Proof depends on

- [Lenzen's deterministic constant-round routing and sorting in the congested clique](congested-clique-constant-round-routing.md)
- [Matrix multiplication in O(n^(1 - 2/omega + eta)) rounds of the congested clique](congested-clique-matrix-multiplication.md)

## Sources

- D. Dolev, C. Lenzen, S. Peled, "Tri, Tri Again: Finding Triangles and Small Subgraphs in a Distributed Setting", DISC 2012, arXiv:1201.6652.
- K. Censor-Hillel, P. Kaski, J. H. Korhonen, C. Lenzen, A. Paz, J. Suomela, "Algebraic Methods in the Congested Clique", PODC 2015; Distributed Computing 32 (2019), arXiv:1503.04963.
- T. Izumi, F. Le Gall, "Triangle Finding and Listing in CONGEST Networks", PODC 2017, arXiv:1705.09061, Theorem 3.
