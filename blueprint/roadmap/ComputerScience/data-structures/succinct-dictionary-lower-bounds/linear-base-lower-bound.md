# Every exact dynamic dictionary makes linearly many probes on the hard distribution

Every deterministic step-indexed cell-probe scheme with words of $w = O(\log U + \log V)$ bits that implements the dynamic dictionary exactly on the admissible histories of the insert–query–delete distribution on $n$ keys makes $\Omega(n)$ expected probes on that distribution, regardless of its space.

## Proof sketch

Each of the $n$ queries must return a value determined by a uniformly random key-value pair, which carries $\Omega(\log U + \log V)$ bits of information not available before the matching insertion; a query reading fewer than one cell written since that insertion would answer independently of it. Since a cell holds $O(\log U + \log V)$ bits, each insertion-query pair forces a constant number of probes in expectation.

## Depends on

- [Hard operation distributions for dynamic dictionaries](hard-operation-distributions.md)
- [Deterministic dynamic cell-probe scheme](../cell-probe-complexity/deterministic-cell-probe-scheme.md)

## Proof depends on

- [Counting bound for cell-probe trees](../cell-probe-complexity/counting-bound-for-cell-probe-trees.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), 2023; arXiv:2306.02253.
- P. B. Miltersen, "Cell Probe Complexity - a Survey", Advances in Data Structures Workshop (FSTTCS pre-conference workshop), 1999.
