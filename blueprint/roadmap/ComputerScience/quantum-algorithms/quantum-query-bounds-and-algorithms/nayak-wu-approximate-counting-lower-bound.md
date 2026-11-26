# Nayak–Wu: quantum lower bound for approximate counting

Let a $T$-query bit-oracle algorithm output, on every $x \in \{0,1\}^N$ of Hamming weight $t$, an estimate $y$ with $|y - t| < \Delta$ with probability at least $1 - \varepsilon$, $2\varepsilon \le 1$. If $1/2 \le \Delta$ and $4\Delta \le N$, then

$$\big(1 - 2\sqrt{\varepsilon(1-\varepsilon)}\big)\Big(\sqrt{\frac{N}{\Delta}} + \frac{\sqrt{t(N - t)}}{\Delta}\Big) \le 16\,T,$$

so approximate counting within additive error $\Delta$ needs $\Omega\big(\sqrt{N/\Delta} + \sqrt{t(N-t)}/\Delta\big)$ queries; for $0 < \Delta \le 1/2$ (exact counting) the corresponding bound is with constant $4$.

## Proof sketch

Apply the weight-layer adversary bound to pairs of layers $a < b$ that the algorithm must distinguish, i.e. with $b - a \ge 2\Delta$, choosing $a, b$ near $t$ and near the extremes to obtain the two terms.

## Depends on

- [Quantum query algorithms with phase and value oracles](../quantum-adversary-methods/quantum-query-algorithms.md)

## Proof depends on

- [Adversary lower bounds for parity, threshold functions and majority](adversary-bounds-for-symmetric-functions.md)

## Sources

- A. Nayak and F. Wu, "The Quantum Query Complexity of Approximating the Median and Related Statistics", STOC 1999.
