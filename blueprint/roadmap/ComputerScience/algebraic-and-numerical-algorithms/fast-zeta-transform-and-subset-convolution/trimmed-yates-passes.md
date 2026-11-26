# Trimmed Yates passes

Fix a duplicate-free list of coordinates and a cardinality threshold $s$. The value of stage $k$ of Yates's algorithm at a set $S$ depends only on the values of stage $k - 1$ at $S$ and at $S$ with coordinate $k$ removed. Consequently, to obtain the stage-$n$ transform on a family $\mathcal{F}$ of sets closed downward in the coordinates processed so far, it suffices to compute each stage only on the sets that differ from a member of $\mathcal{F}$ in already processed coordinates; for ranked inputs supported on sets of size at most $t$, all stage values at sets of size below $s$ can be precomputed once and reused, and stage values at a query set $C$ of size at least $s$ need only the subsets of $C$ of size at least $s$, enumerated as complements within $C$ of the subsets of size at most $|C| - s$.

## Depends on

- [Yates's algorithm computes zeta and Möbius transforms in n 2^n operations](yates-algorithm.md)

## Sources

- A. Björklund, T. Husfeldt, P. Kaski and M. Koivisto, "Trimmed Moebius Inversion and Graphs of Bounded Degree", Theory of Computing Systems 47(3), 2010.
- T. M. Chan, R. Itakura, Z. Ma and Y. Yu, "3SUM Made Simpler (Without Matrix Multiplication), k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized", arXiv:2610.42012v1, 2026.
