# Greedy open addressing and uniform probing

In the model of open-addressing insertion without reordering, an insertion algorithm is *greedy* if every key is placed in the first unoccupied slot of its probe sequence, so that its probe complexity equals its insertion time. *Uniform probing* is the greedy table whose probe sequence $h_1(x), \dots, h_n(x)$ is a uniformly random permutation of $[n]$, independently for every key.

## Depends on

- [Open-addressing insertion without reordering](oa-without-reordering-model.md)

## Sources

- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
- Jeffrey D. Ullman, "A Note on the Efficiency of Hashing Functions", Journal of the ACM 19(3) (1972).
