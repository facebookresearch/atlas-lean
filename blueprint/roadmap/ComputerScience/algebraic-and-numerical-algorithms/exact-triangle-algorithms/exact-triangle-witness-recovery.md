# Witness recovery from modular lopsided answers

Given correct answers to the lopsided triangle queries of the modular splitting, scan each accepted (outer pair, piece) by checking the original integer weights $A_{ij} + B_{jk} + C_{ik}$ for all $k$ in the piece. The scan finds a zero triangle whenever one exists, and the number of failed scans is at most the false positive count $F_p$, so the total scanning cost is at most $(F_p + 1)$ times the piece size, which is $O(\sqrt{D})$.

## Proof sketch

Every failed scan of an accepted piece contains at least one triangle that is zero mod $p$ but nonzero, and distinct failed scans contain distinct such triangles.

## Depends on

- [Splitting Exact Triangle into lopsided triangle queries](exact-triangle-modular-splitting.md)

## Proof depends on

- [A minimum-count prime has few false positives](minimum-count-prime-selection.md)

## Sources

- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", 2026.
