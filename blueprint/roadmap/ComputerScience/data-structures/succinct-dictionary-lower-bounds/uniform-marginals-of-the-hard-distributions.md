# Uniform marginals of the hard dictionary distributions

Under the insert–query–delete and insert–delete distributions on $n$ keys, for every time step the set of present keys is uniformly distributed among the $n$-subsets of $[U]$ given the deleted keys' positions, the values of the present keys are independent and uniform in $[V]$, and permuting the universe or shifting values maps the distribution to itself. Consequently any memory state decodes to a dictionary whose multiplicity among all reachable states is controlled by $\binom{U}{n} V^n$, which is what the entropy arguments compare with the memory size.

## Proof sketch

The keys are an injective uniform sequence and the values are independent uniform, so the joint law is invariant under permutations of $[U]$ and translations of values modulo $V$; the set of keys present at a fixed step is the image of a fixed set of positions under the random injection.

## Depends on

- [Hard operation distributions for dynamic dictionaries](hard-operation-distributions.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), 2023; arXiv:2306.02253.
