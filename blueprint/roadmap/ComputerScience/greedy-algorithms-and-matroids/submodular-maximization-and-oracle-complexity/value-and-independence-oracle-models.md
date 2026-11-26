# Value and independence oracle models

In the **value oracle model** an algorithm accesses an unknown set function $f : 2^E \to \beta$ only through queries "what is $f(S)$?" for finite $S \subseteq E$; in the **independence oracle model** it accesses a matroid (or independence system) only through queries "is $S$ independent?". The **query complexity** of a deterministic algorithm on an input is the number of queries along its computation path; all other computation is free. Two oracles that agree on all queried sets lead the algorithm along the same path to the same output.

## Depends on

- [Submodular set function](../../approximation-algorithms/maximum-n-times-coverage/is-submodular.md)
- [Greedy algorithm on a matroid](../matroid-greedy-algorithm/matroid-greedy.md)

## Sources

- G. L. Nemhauser and L. A. Wolsey, "Best Algorithms for Approximating the Maximum of a Submodular Set Function", Mathematics of Operations Research 3(3), 1978.
- G. L. Nemhauser, L. A. Wolsey and M. L. Fisher, "An Analysis of Approximations for Maximizing Submodular Set Functions I", Mathematical Programming 14, 1978.
