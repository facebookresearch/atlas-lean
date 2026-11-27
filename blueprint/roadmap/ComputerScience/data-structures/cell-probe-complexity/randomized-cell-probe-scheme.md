# Randomized cell-probe scheme with private coins

A *randomized cell-probe scheme* consists of a probability distribution on initial memories and, for each operation, a cell-probe tree that may additionally contain coin nodes branching on a uniformly random bit; coin nodes cost no probes. Against a fixed (oblivious) distribution $\mathcal{D}$ on operation sequences, the *expected probe count* is the expectation of the probe count over $\mathcal{D}$, the initial memory and all coins.

The scheme is *zero-error* (Las Vegas) on a set $C$ of sequences if every run with positive probability on a sequence in $C$ returns the correct answers; it is *bounded-error* (Monte Carlo) if each answer is correct with probability at least $1 - \varepsilon$.

## Depends on

- [Deterministic dynamic cell-probe scheme](deterministic-cell-probe-scheme.md)
- [Las Vegas and Monte Carlo algorithms](../../randomized-algorithms/probabilistic-analysis-tools/las-vegas-and-monte-carlo-algorithms.md)

## Sources

- P. B. Miltersen, "Cell Probe Complexity - a Survey", Advances in Data Structures Workshop (FSTTCS pre-conference workshop), 1999.
- A. C.-C. Yao, "Probabilistic Computations: Toward a Unified Measure of Complexity", Proceedings of the 18th IEEE Symposium on Foundations of Computer Science (FOCS), 1977.
