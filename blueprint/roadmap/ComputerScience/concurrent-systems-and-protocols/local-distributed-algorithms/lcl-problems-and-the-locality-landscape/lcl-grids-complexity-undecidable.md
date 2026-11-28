# LCL complexities on grids and undecidability of their classification

Consider input-free LCL problems on toroidal $d$-dimensional grids with equal side lengths and a consistent orientation, in the deterministic LOCAL model with unique identifiers; for $d = 2$ these are $n \times n$ tori with $N = n^2$ vertices. Every such LCL on two-dimensional tori has deterministic complexity $O(1)$, $\Theta(\log^* n)$ or $\Theta(n)$: the gap between $\omega(\log^* n)$ and $o(n)$ is proved by a speedup lemma for grids, and the gap between $\omega(1)$ and $o(\log^* n)$, for oriented grids of every fixed dimension, is due to Grunau, Rozhoň and Brandt. It is undecidable, even under the promise that the complexity is $\Theta(\log^* n)$ or $\Theta(n)$, which of the two holds for a given LCL on two-dimensional tori. For every fixed $d \ge 2$, $4$-colouring $d$-dimensional grids has complexity $\Theta(\log^* n)$, by a direct proof; computer search additionally synthesizes normal-form algorithms for specific $\Theta(\log^* n)$ problems. This classification concerns deterministic algorithms; randomized complexity is not covered.

## Proof sketch

The speedup and the normal form: any $o(n)$-round algorithm can be converted into one that first computes a maximal independent set of a large constant power of the grid in $O(\log^* n)$ rounds and then applies a finite local rule to the resulting Voronoi tiles, which a finite search can attempt to synthesize. Undecidability: for each Turing machine $M$, the LCL $L_M$ is the disjoint union of $3$-colouring, which always has a solution but needs $\Theta(n)$ rounds, and a problem asking to label the grid with tiles containing the execution table of $M$ started on the empty tape. If $M$ halts, the second problem is solved in $O(\log^* n)$ rounds by tiles around an MIS of a power of the grid; if $M$ does not halt, no such finite tiles exist and $L_M$ needs $\Theta(n)$ rounds. So $L_M$ has complexity $\Theta(\log^* n)$ exactly when $M$ halts.

## Depends on

- [Deterministic and randomized LOCAL complexity of an LCL problem](lcl-deterministic-randomized-complexity.md)

## Proof depends on

- [LCL complexity gaps between constant and log-star](lcl-gap-constant-versus-log-star.md)
- [Deterministic LCL complexities between log-star and log n collapse](lcl-deterministic-gap-log-star-log-n.md)

## Sources

- S. Brandt, J. Hirvonen, J. H. Korhonen, T. Lempiäinen, P. R. J. Östergård, C. Purcell, J. Rybicki, J. Suomela, P. Uznański, "LCL problems on grids", PODC 2017, arXiv:1702.05456, Theorems 2, 3 and 4 and Section 6.
- C. Grunau, V. Rozhoň, S. Brandt, "The Landscape of Distributed Complexities on Trees and Beyond", PODC 2022, arXiv:2202.04724, abstract.
