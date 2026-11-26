# Strings with $\gamma = \Omega(\delta\log(n/\delta))$

For every length $n$ and every value $\delta \ge 2$ there is a string $T$ of length $n$ with $\delta(T) \le \delta$ and $\gamma(T) = \Omega(\delta \log\frac{n}{\delta})$. Hence $\delta$ can be asymptotically smaller than every measure lower-bounded by $\gamma$, and no representation in $O(\gamma)$ words can be guaranteed in terms of $\delta$.

## Proof sketch

Take a string that combines $\delta$ independent blocks, each built from a Fibonacci-like or doubling construction with $\Theta(\log(n/\delta))$ distinct square-free-like extensions, so that the number of length-$k$ substrings stays $O(k\delta)$ while each block forces its own attractor positions at $\Theta(\log(n/\delta))$ different scales, since substrings of each scale have a unique occurrence region.

## Depends on

- [Substring complexity $\delta$](substring-complexity.md)
- [String attractors](string-attractor.md)

## Proof depends on

- [Substring complexity is at most the attractor size](delta-at-most-gamma.md)

## Sources

- Tomasz Kociumaka, Gonzalo Navarro, Nicola Prezza, "Toward a Definitive Compressibility Measure for Repetitive Sequences", IEEE Transactions on Information Theory 69(4) (2023); LATIN (2020), arXiv:1910.02151.
