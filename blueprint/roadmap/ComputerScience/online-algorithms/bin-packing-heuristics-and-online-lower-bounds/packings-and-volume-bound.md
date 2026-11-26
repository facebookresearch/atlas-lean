# Packings and the volume bound

An instance of bin packing is a list $\ell$ of item sizes $a_i \in \mathbb{N}$ and a capacity $C$ with every $a_i \le C$. A **packing** is a list of bins, each a list of items, which together hold exactly the items of $\ell$ counted with multiplicity and each of total size at most $C$; $\mathrm{OPT}$ is the minimum number of bins. Every packing uses at least $\lceil \sum_i a_i / C \rceil$ bins. Two bins are **jointly overfull** if their contents do not fit together into one bin.

## Depends on

- [Bin packing instances](../../../TheoryOfComputation/np-completeness/number-and-packing-problems/bin-packing/bin-packing-instance.md)

## Sources

- D. P. Williamson and D. B. Shmoys, "The Design of Approximation Algorithms", Cambridge University Press, 2011.
