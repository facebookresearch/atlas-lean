# LCL complexities on grids and undecidability of their classification

On $d$-dimensional toroidal grids with $n$ vertices (with consistent orientation), every LCL problem has deterministic LOCAL complexity $O(1)$, $\Theta(\log^* n)$, or $\Theta(n^{1/d})$ (the diameter scale), and randomness does not help. Determining which of these classes a given LCL problem on two-dimensional grids belongs to is undecidable; more precisely, it is undecidable whether a given LCL on oriented two-dimensional grids is solvable in $O(\log^* n)$ rounds. Some LCLs on grids with complexity $\Theta(\log^* n)$, such as $4$-colouring of the two-dimensional grid, are proved to be in that class only by computer-assisted search for normal-form algorithms.

## Proof sketch

Gaps follow from a normal form: any $o(n^{1/d})$-round algorithm can be converted into one that first computes a maximal independent set of a large power of the grid in $O(\log^* n)$ rounds, then applies a finite local rule depending only on the positions of nearby MIS vertices, which a finite search can attempt to synthesize. Undecidability reduces from the tiling (domino) problem: an LCL encodes tilings so that a fast algorithm exists if and only if the tile set admits periodic-like local solutions in all large tori.

## Depends on

- [Deterministic and randomized LOCAL complexity of an LCL problem](lcl-deterministic-randomized-complexity.md)

## Proof depends on

- [No LCL complexities between constant and log-star](lcl-gap-constant-versus-log-star.md)
- [Deterministic LCL complexities between log-star and log n collapse](lcl-deterministic-gap-log-star-log-n.md)

## Sources

- S. Brandt, J. Hirvonen, J. H. Korhonen, T. Lempiäinen, P. R. J. Östergård, C. Purcell, J. Rybicki, J. Suomela, P. Uznański, "LCL problems on grids", PODC 2017, arXiv:1702.05456.
