# Quota selection with admissibility tests

**Quota selection.** Items $x_1, \dots, x_n$ are partitioned into groups by a known map $g$. Each item carries a hidden weight $w(x)$, injective into a linear order, and a hidden admissibility bit. The **representative** of a group containing an admissible item is its lightest admissible item. Given a quota $k$, the task is to output the $k$ lightest representatives (all of them if there are fewer than $k$), where weights may be accessed only by pairwise comparisons and admissibility only by tests on single items.

## Depends on

- [Median-of-medians selection](../median-of-medians/median-of-medians.md)

## Sources

- T. M. Chan, R. Itakura, Z. Ma and Y. Yu, "3SUM Made Simpler (Without Matrix Multiplication), k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized", arXiv:2610.42012, 2026.
- M. Blum, R. W. Floyd, V. Pratt, R. L. Rivest and R. E. Tarjan, "Time Bounds for Selection", Journal of Computer and System Sciences 7(4), 1973.
