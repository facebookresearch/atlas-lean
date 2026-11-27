# Triangle detection in the congested clique in sublinear rounds

In the congested clique, a deterministic algorithm detects and lists all triangles of the input graph in $O(n^{1/3} / \log n)$ rounds; deciding whether a triangle exists can be done in $O(n^{1 - 2/\omega + \eta})$ rounds for every fixed $\eta > 0$, which is $O(n^{0.158})$ with $\omega < 2.3729$. Listing all triangles requires $\Omega(n^{1/3}/\log n)$ rounds, since some processor must output a $1/n$ fraction of up to $\Theta(n^3)$ triangles while learning only $O(n \log n)$ bits per round.

## Proof sketch

Partition the vertex set into $n^{1/3}$ parts and assign each of the $n$ triples of parts to one processor, which must learn the $O(n^{4/3})$ edges between its three parts; each processor holds $O(n)$ edges and needs to send each to $O(n^{1/3})$ processors, so Lenzen-style routing finishes in $O(n^{1/3}/\log n)$ rounds after packing edges into messages. The listing lower bound is a counting argument: a processor listing $\Omega(n^2)$ triangles must know $\Omega(n^{4/3})$ edges.

## Depends on

- [The congested clique model](the-congested-clique-model.md)
- [Matrix multiplication exponent](../../../../TheoryOfComputation/algebraic-complexity/matrix-multiplication-exponent/matrix-multiplication-exponent.md)

## Proof depends on

- [Lenzen's deterministic constant-round routing and sorting in the congested clique](congested-clique-constant-round-routing.md)
- [Matrix multiplication in O(n^(1 - 2/omega + eta)) rounds of the congested clique](congested-clique-matrix-multiplication.md)

## Sources

- D. Dolev, C. Lenzen, S. Peled, "Tri, Tri Again: Finding Triangles and Small Subgraphs in a Distributed Setting", DISC 2012, arXiv:1201.6652.
- K. Censor-Hillel, P. Kaski, J. H. Korhonen, C. Lenzen, A. Paz, J. Suomela, "Algebraic Methods in the Congested Clique", PODC 2015; Distributed Computing 32 (2019), arXiv:1503.04963.
