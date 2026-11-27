# Some equational theory has decidable unifiability of single equations but not of systems

For elementary unification, single equations can be easier than systems: for some equational theory unifiability of single elementary equations is decidable, but unifiability of elementary systems of several equations is undecidable.

**Theorem (Narendran and Otto).** There is an equational theory $E$ such that unifiability of elementary $E$-unification problems of cardinality $1$ is decidable, but unifiability of elementary $E$-unification problems of larger cardinality is undecidable (see [E-unification problems](equational-unification-problems.md)).

For general unification no such gap exists, since a system $\{s_i =^?_E t_i\}_{i \leq n}$ has the same unifiers as the single equation $f(s_1, \dots, s_n) =^?_E f(t_1, \dots, t_n)$ with a fresh symbol $f$.

## Depends on

- [E-unification problems](equational-unification-problems.md)

## Proof depends on

None.

## Expansion

The copy read states the theorem without proof, citing Narendran and Otto; the construction of the theory is not reproduced here. The source places this result beside a similar phenomenon for unification types: some theory has minimal complete sets of unifiers for all elementary single equations but is of type zero because of a system of two equations (Bürckert, Herold and Schmidt-Schauß).

## Sources

- P. Narendran and F. Otto, "Some results on equational unification", in *10th International Conference on Automated Deduction (CADE-10)*, Lecture Notes in Computer Science 449, Springer, 1990, pp. 276–291, doi:10.1007/3-540-52885-7_94 (original source, cited beside the copy read).
- F. Baader and W. Snyder, "Unification theory", in A. Robinson and A. Voronkov (eds.), *Handbook of Automated Reasoning*, Vol. I, Elsevier, 2001, Chapter 8, pp. 445–533, doi:10.1016/B978-044450813-3/50010-2; read in the authors' open-access copy at <https://lat.inf.tu-dresden.de/research/papers/2001/BaaderSnyderHandbook.pdf>: Section 3.2.3 ("Single equations versus systems of equations"), which states the theorem.
