# Query bounds for quota selection

There is a deterministic algorithm for quota selection that, on every instance with $n$ items and quota $k$, returns exactly the $\min(k, R)$ lightest representatives (where $R$ is the number of groups containing an admissible item), using $O(n)$ comparisons in total and charging each admissibility test either to a returned representative or to an item that fails its test; in particular every item is tested at most once.

## Proof sketch

Scan items in increasing weight order produced by linear-time selection on geometrically shrinking candidate sets; an item is tested only when it is the lightest untested item of a group that has no representative yet, so passing tests produce representatives and failing tests are charged to the failing item.

## Depends on

- [Quota selection with admissibility tests](quota-selection-with-admissibility-tests.md)

## Proof depends on

- [Correctness of median-of-medians selection](../median-of-medians/median-of-medians-correct.md)

## Sources

- T. M. Chan, R. Itakura, Z. Ma and Y. Yu, "3SUM Made Simpler (Without Matrix Multiplication), k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized", arXiv:2610.42012, 2026.
- M. Blum, R. W. Floyd, V. Pratt, R. L. Rivest and R. E. Tarjan, "Time Bounds for Selection", Journal of Computer and System Sciences 7(4), 1973.
