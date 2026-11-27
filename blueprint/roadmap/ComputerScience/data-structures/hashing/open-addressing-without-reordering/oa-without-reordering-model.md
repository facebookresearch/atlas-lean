# Open-addressing insertion without reordering

Fix an array of $n$ slots and a parameter $\delta \in (0, 1)$ such that $\delta n$ is a positive integer, the number of slots left free at the end; in particular $\delta \ge 1/n$. Keys $x_1, \dots, x_m$ with $m = n - \delta n$ are inserted one after another. Each key $x$ carries an infinite *probe sequence* $h_1(x), h_2(x), \dots \in [n]$; the probe sequences of distinct keys are independent draws from a fixed distribution $P$. An *insertion algorithm* $\mathcal{A}$ places $x_i$ into some slot $h_j(x_i)$ that is unoccupied at that moment, and it never moves a key inserted earlier (no reordering). The pair $(P, \mathcal{A})$ is an *open-addressed hash table without reordering*. If $x_i$ is stored in $h_j(x_i)$ with $j$ minimal among the indices naming that slot, its *probe complexity* is $j$: a query can find $x_i$ with $j$ probes. The *insertion time* of $x_i$ is the number of slots $\mathcal{A}$ inspects while inserting it.

## Depends on

- [Open-addressing hash table](../open-addressing/open-addressing.md)

## Sources

- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
- Andrew C. Yao, "Uniform Hashing Is Optimal", Journal of the ACM 32(3) (1985).
