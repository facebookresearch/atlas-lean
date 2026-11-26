# Nayak–Wu: quantum lower bounds for approximate median and k-th smallest

Let a $T$-query value-oracle algorithm over a linearly ordered alphabet, on inputs $x \in \Sigma^N$, output an element whose rank is within $\Delta$ of $k$ (resp. a $\delta$-approximate median, $0 < \delta < 1$), with error $\varepsilon \le 1/2$. Then for $1 \le k \le N$, $1 \le \Delta$, $4\Delta \le N$:

$$\big(1 - 2\sqrt{\varepsilon(1 - \varepsilon)}\big)\Big(\sqrt{\frac{N}{\Delta}} + \frac{\sqrt{k(N-k)}}{\Delta}\Big) \le 32\, T, \qquad \big(1 - 2\sqrt{\varepsilon(1-\varepsilon)}\big)\min\Big(\frac{1}{\delta}, N\Big) \le 24\, T$$

for selection and the median respectively (with improved constants $16$ and $12$ when the oracle steps are involutions). The same bounds hold, with $T$ replaced by $T + 1$, for algorithms returning an index of such an element.

## Proof sketch

Reduce from distinguishing weight layers of a Boolean string: map a bit string to a sequence over a two-element-valued ordered alphabet so that the rank of the answer reveals the Hamming weight up to $\Delta$, and simulate one value query with one bit query.

## Depends on

- [Quantum query algorithms with phase and value oracles](../quantum-adversary-methods/quantum-query-algorithms.md)

## Proof depends on

- [Adversary lower bounds for parity, threshold functions and majority](adversary-bounds-for-symmetric-functions.md)
- [Nayak–Wu: quantum lower bound for approximate counting](nayak-wu-approximate-counting-lower-bound.md)

## Sources

- A. Nayak and F. Wu, "The Quantum Query Complexity of Approximating the Median and Related Statistics", STOC 1999.
