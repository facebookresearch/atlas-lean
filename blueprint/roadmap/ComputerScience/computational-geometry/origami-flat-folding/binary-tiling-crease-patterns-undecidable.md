# Flat foldability of binary-tiling crease patterns is undecidable

No algorithm decides, given a finite set of creases, whether the infinite crease pattern obtained by placing a scaled copy of it in every tile of the square binary tiling is flat-foldable. This holds for labeled and for unlabeled creases, with no boundary constraints.

**Theorem (Eppstein).** The following problem is undecidable: given a finite set of (labeled, or unlabeled) creases for a tile, is the crease pattern on a square of origami paper that has a scaled copy of these creases in each tile of the square binary tiling flat-foldable?

The *square binary tiling* is the recursive self-similar subdivision of a square into $2 \times 1$ rectangles in which one rectangle covers the upper half of the square and the lower left and lower right quadrants are each subdivided in the same pattern as the whole square (Section 6.3 of the source). Each rectangle has two children adjacent to its bottom edge, a parent above it (except the topmost rectangle), and left and right neighbors along its sides. The copy in each tile is the input pattern scaled (and translated) to that rectangle. An instance is a finite list of creases in the $2 \times 1$ tile, each a line segment given by rational endpoint coordinates, with a mountain or valley label in the labeled version; the source fixes no encoding, and the undecidable instances its proof builds have this form, their creases lying on a fine square grid of the tile. The finite tile pattern is the input, in contrast with the companion result for a fixed infinite crease pattern with a finite boundary specification as input. The proof reduces from Kari's binary Wang tiling problem (Lemma 24 of the source).

## Depends on

- [Flat foldings of crease patterns](flat-foldings-of-crease-patterns.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The reduction is from the binary Wang tiling problem, proved undecidable by Kari: given finitely many prototiles with colored edges for the binary tiling (each tile has five edges), can every tile be assigned a prototile with matching colors on shared edges? By König's lemma, tiling the square binary tiling, every binary tiling of the half-plane, or every finite union of their tiles are equivalent (Lemma 23 of the source carries Kari's result from the hyperbolic binary tiling to the square). For each tile a Boolean circuit reads the colors of its edges, shared with neighboring tiles, and checks that they match a prototile; converting the circuit into creases with the folding gadgets gives a finite pattern that folds flat in a tile exactly when the check succeeds. The repeated pattern is flat-foldable if and only if the Wang tiling instance has a solution.

A good expansion links pages for the undecidability of binary Wang tiling (Kari; Lemma 24 of the source) and its transfer to the square binary tiling (Lemma 23), for the pleat and circuit gadgets of Akitaya et al. that turn each tile's circuit into a finite crease pattern as in Theorem 6, for the width relation at junctions of three variable gadgets that lets the scaled gadgets of neighbouring rectangles connect (Lemma 19), and for the reduction of flat foldability of a tame crease pattern to its nearby regions (Lemma 17), which the "if" direction uses to build a global folding.

## Sources

- David Eppstein, "Computational Complexities of Folding", Journal of Information Processing 33, pp. 954–973, 2025, <https://doi.org/10.2197/ipsjjip.33.954>; read in arXiv:2410.07666v1, <https://arxiv.org/abs/2410.07666v1>: Section 6.3 (the binary tiling), Lemmas 17 and 19, the proof of Theorem 6, Theorem 7 and Section 6.8 ("Wang tiling", with Lemmas 23 and 24), in the numbering of that version.
- Jarkko Kari, "The Tiling Problem Revisited (Extended Abstract)", Machines, Computations, and Universality (MCU 2007), Lecture Notes in Computer Science 4664, pp. 72–79, 2007, <https://doi.org/10.1007/978-3-540-74593-8_6>; undecidability of binary Wang tiling; cited for attribution, the result as read in Section 6.8 of David Eppstein's paper above (arXiv:2410.07666v1).
