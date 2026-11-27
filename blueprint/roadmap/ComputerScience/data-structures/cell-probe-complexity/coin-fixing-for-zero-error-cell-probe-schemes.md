# Coin fixing for zero-error randomized cell-probe schemes

Let $P$ be a randomized cell-probe scheme in $S$ cells of $w$ bits that is zero-error on a set $C$ of operation sequences, and let $\mathcal{D}$ be a probability distribution on sequences of bounded length over a finite operation alphabet (fixed in advance, independently of the coins). Then there is a deterministic step-indexed cell-probe scheme $P'$ in the same $S$ cells that is correct on every sequence in $C$ and whose expected probe count under $\mathcal{D}$ is at most that of $P$. If $P$ draws all of its randomness in the initial memory, $P'$ can be taken time-invariant.

Consequently, a lower bound on the expected probes of deterministic step-indexed schemes under $\mathcal{D}$ is a lower bound for zero-error randomized schemes.

## Proof sketch

Every randomized tree is a finite mixture of deterministic trees indexed by its coin outcomes, and the initial memory distribution is a mixture of fixed memories. Since $\mathcal{D}$ does not depend on the coins, the expected probe count is an average, over independent per-step coin assignments and initial memories, of the expected probe count of the corresponding deterministic step-indexed scheme. Some point of the support achieves at most the average, and zero error means every supported assignment is correct on $C$. This is the easy direction of Yao's principle.

## Depends on

- [Randomized cell-probe scheme with private coins](randomized-cell-probe-scheme.md)
- [Deterministic dynamic cell-probe scheme](deterministic-cell-probe-scheme.md)

## Proof depends on

- [Yao's minimax principle](../../../TheoryOfComputation/randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Sources

- A. C.-C. Yao, "Probabilistic Computations: Toward a Unified Measure of Complexity", Proceedings of the 18th IEEE Symposium on Foundations of Computer Science (FOCS), 1977.
- P. B. Miltersen, "Cell Probe Complexity - a Survey", Advances in Data Structures Workshop (FSTTCS pre-conference workshop), 1999.
