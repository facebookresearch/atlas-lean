# Uniform marginals of the hard dictionary distributions

Under the insert–query–delete and insert–delete distributions on $n$ keys, after the initial insertions and after every meta-operation the set of present keys is uniformly distributed among the $n$-subsets of $[U]$, also conditionally on the deletion permutation $\pi$, and the values of the present keys are independent and uniform in $[V]$ and independent of the key set. Moreover, the joint law is invariant under permutations of $[U]$ applied to all keys and under translations of all values modulo $V$. Consequently the dictionary contents at such a time have entropy exactly $\log_2 \binom{U}{n} + n \log_2 V$, the quantity that the entropy arguments compare with the memory size.

## Proof sketch

The keys are a uniform injective sequence and the values are independent uniform, both independent of $\pi$, so the joint law is invariant under permutations of $[U]$ and translations of values modulo $V$. The set of keys present at a fixed time is the image of a fixed set of $n$ positions, determined by $\pi$, under the random injection, hence uniform among $n$-subsets for every value of $\pi$.

## Depends on

- [Hard operation distributions for dynamic dictionaries](hard-operation-distributions.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 1842-1862, 2023; arXiv:2306.02253.
