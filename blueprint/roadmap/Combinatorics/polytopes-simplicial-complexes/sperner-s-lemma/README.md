# Sperner's lemma

Colour the vertices of a triangulated simplex so that each vertex avoids the colours of the corners not spanning its smallest face. Sperner's lemma (1928) says that an odd number of cells, and so at least one, carry all colours. The proof is a parity argument on "doors" (faces with all colours but one), which is also a path-following argument: walking through doors from the boundary leads to a fully coloured cell. Sperner's lemma gives the Knaster–Kuratowski–Mazurkiewicz lemma and Brouwer's fixed-point theorem, and its path-following proof is the archetype of the complexity class PPAD. The pages below state the one-dimensional lemma and the two-dimensional lemma for the triangulation of a triangle by the unit grid; the general $n$-dimensional lemma on iterated barycentric subdivisions is the main step in the proof of the Knaster–Kuratowski–Mazurkiewicz lemma.

- [Sperner's lemma in dimension one](odd-card-bichromatic.md)
- [Rainbow triple of colours](is-rainbow.md)
- [Up cells of the grid triangulation](up-cells.md)
- [Down cells of the grid triangulation](down-cells.md)
- [Sperner colouring of the grid triangle](is-sperner-colouring.md)
- [Sperner's lemma in dimension two (parity form)](odd-card-rainbow.md)
- [Sperner's lemma in dimension two](exists-rainbow.md)

## Related topics

- [Brouwer fixed-point theorem](../../../Topology/algebraic-topology/brouwer-fixed-point-theorem/README.md): proved from the $n$-dimensional lemma through the Knaster–Kuratowski–Mazurkiewicz lemma.
- [PPAD and the END-OF-THE-LINE problem](../../../TheoryOfComputation/completeness-other-classes/ppad-and-the-end-of-the-line-problem/README.md): the complexity class defined by this kind of parity argument; Papadimitriou (1994) showed the three-dimensional Sperner problem PPAD-complete (Daskalakis, Goldberg and Papadimitriou 2009 list Sperner among the PPAD-complete problems of that paper).
