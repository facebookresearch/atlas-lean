# Counting bound for cell-probe trees

Let $T$ be a cell-probe tree over $S$ cells of $w$ bits with depth $d$.

1. The path followed by $T$ on a memory $m$, hence its returned value and the sequence of writes it performs, depends only on the contents of the at most $d$ distinct cells probed along the run on $m$; in particular, two memories agreeing on those cells give the same value, and their final memories agree on the probed cells and are each unchanged elsewhere.
2. $T$ has at most $2^{w d}$ leaves, so if the map $m \mapsto (\text{value returned by } T \text{ on } m)$ (the leaf label) takes $N$ distinct values then $N \le 2^{wd}$, i.e. $d \ge \log_2 N / w$.

## Proof sketch

Both statements follow by induction on the tree. A read node branches $2^w$ ways and a write node one way, so a tree of depth $d$ has at most $(2^w)^d$ leaves. A run is determined by the answers to its reads, which are contents of the probed cells, and a write changes only the cell it names, so cells never probed keep their initial contents.

## Depends on

- [Adaptive cell-probe decision tree](adaptive-cell-probe-decision-tree.md)

## Sources

- P. B. Miltersen, "Cell Probe Complexity - a Survey", Advances in Data Structures Workshop (FSTTCS pre-conference workshop), 1999.
