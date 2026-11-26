# Trimmed Yates passes

Fix a duplicate-free list of coordinates. The value of stage $k$ of Yates's algorithm at a set $S$ depends only on the values of stage $k - 1$ at $S$ and at $S$ with coordinate $k$ removed. Consequently, to obtain the stage-$n$ transform on a family $\mathcal{F}$ of sets closed downward in the coordinates processed so far, it suffices to compute each stage only on the sets that differ from a member of $\mathcal{F}$ in already processed coordinates.

## Depends on

- [Yates's algorithm computes zeta and Möbius transforms in n 2^n operations](yates-algorithm.md)

## Sources

- A. Björklund, T. Husfeldt, P. Kaski and M. Koivisto, "Trimmed Moebius Inversion and Graphs of Bounded Degree", Theory of Computing Systems 47(3), 2010.
