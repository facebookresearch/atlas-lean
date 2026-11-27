# Every exact dynamic dictionary makes linearly many probes on the hard distribution

For $V \ge 2$, every deterministic step-indexed cell-probe scheme with words of $w = O(\log U + \log V)$ bits that implements the dynamic dictionary exactly on the admissible histories of the insert–query–delete distribution on $n$ keys makes $\Omega(n)$ expected probes on that distribution, regardless of its space.

## Proof sketch

A probe tree that makes no probe returns a fixed leaf label. For a fixed key $x$ and step index, admissible histories of the same length end with $x$ stored under different values (here $V \ge 2$ is used), so the tree that answers $\mathrm{query}(x)$ at that step must make at least one probe. Hence each of the $n$ queries of the distribution makes at least one probe, on every outcome.

## Depends on

- [Hard operation distributions for dynamic dictionaries](hard-operation-distributions.md)
- [Deterministic dynamic cell-probe scheme](../cell-probe-complexity/deterministic-cell-probe-scheme.md)

## Proof depends on

- [Adaptive cell-probe decision tree](../cell-probe-complexity/adaptive-cell-probe-decision-tree.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 1842-1862, 2023; arXiv:2306.02253.
- P. B. Miltersen, "Cell Probe Complexity - a Survey", Advances in Data Structures Workshop (FSTTCS pre-conference workshop), 1999.
