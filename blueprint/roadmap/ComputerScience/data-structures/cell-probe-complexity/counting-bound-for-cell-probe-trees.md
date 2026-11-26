# Counting bound for cell-probe trees

Let $T$ be a cell-probe tree over $S$ cells of $w$ bits with depth $d$.

1. The value and final memory returned by $T$ on a memory $m$ depend only on the contents of the at most $d$ distinct cells probed along the run on $m$; in particular, two memories agreeing on those cells give the same result.
2. $T$ has at most $2^{w d}$ leaves, so if the map $m \mapsto (\text{result of } T \text{ on } m)$ takes $N$ distinct values then $N \le 2^{wd}$, i.e. $d \ge \log_2 N / w$.

## Proof sketch

Both statements follow by induction on the tree. A read node branches $2^w$ ways and a write node one way, so a tree of depth $d$ has at most $(2^w)^d$ leaves. A run is determined by the answers to its reads, which are contents of the probed cells, and a write only changes cells that later reads on the same path observe.

## Depends on

- [Adaptive cell-probe decision tree](adaptive-cell-probe-decision-tree.md)

## Proof depends on

- [A binary tree with n! leaves has height at least log n!](../../sorting-and-searching/lower-bound-for-comparison-sorting/factorial-le-two-pow-height.md)

## Sources

- P. B. Miltersen, "Cell Probe Complexity - a Survey", Advances in Data Structures Workshop (FSTTCS pre-conference workshop), 1999.
