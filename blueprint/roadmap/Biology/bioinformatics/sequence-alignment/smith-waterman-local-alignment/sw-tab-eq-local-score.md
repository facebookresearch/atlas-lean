# The table computes the optimal local alignment score

If $g \le 0$, then for all sequences $x, y$ the [table value](sw-tab.md) equals the [local score](../pairwise-sequence-alignment/local-score.md): the maximum over pairs of infixes of $x$ and $y$ (the empty ones included, which give the floor $0$) of their [Needleman–Wunsch score](../pairwise-sequence-alignment/nw-score.md) (Smith–Waterman 1981).

## Sources

- T. F. Smith and M. S. Waterman, *Identification of common molecular subsequences*, J. Mol. Biol. 147 (1981), 195–197.
