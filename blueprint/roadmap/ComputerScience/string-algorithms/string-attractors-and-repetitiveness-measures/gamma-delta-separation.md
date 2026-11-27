# Strings with $\gamma = \Omega(\delta\log(n/\delta))$

For every length $n$ and every value $\delta \ge 2$ there is a string $T$ of length $n$ with $\delta(T) \le \delta$ and $\gamma(T) = \Omega(\delta \log\frac{n}{\delta})$. Hence $\delta$ can be asymptotically smaller than every measure lower-bounded by $\gamma$, and no representation in $O(\gamma)$ words can be guaranteed in terms of $\delta$.

## Proof sketch

Let $S_\infty$ have $\mathtt{b}$ at the positions $2^j$ ($j \ge 0$) and $\mathtt{a}$ elsewhere, and let $S_n$ be its length-$n$ prefix. Beyond position $2^{j-1}$ consecutive $\mathtt{b}$'s are at distance at least $2^j$, so $d_k(S_n) \le 2^{\lceil\log k\rceil - 1} + k + 1 \le 2k$ and $\delta(S_n) \le 2$; each $\mathtt{b}\mathtt{a}^{2^j-1}\mathtt{b}$ occurs only at $[2^j, 2^{j+1}]$, and these regions are disjoint for even $j$, so $\gamma(S_n) \ge \frac12\lfloor\log n\rfloor$. Concatenating $m = \Theta(\delta)$ such strings of length $\Theta(n/m)$ over disjoint alphabets, separated by distinct delimiters, gives $\delta = O(m)$ and $\gamma = \Omega(m\log(n/m))$.

## Depends on

- [Substring complexity $\delta$](substring-complexity.md)
- [String attractors](string-attractor.md)

## Proof depends on

- [Substring complexity is at most the attractor size](delta-at-most-gamma.md)

## Sources

- Tomasz Kociumaka, Gonzalo Navarro, Nicola Prezza, "Toward a Definitive Compressibility Measure for Repetitive Sequences", IEEE Transactions on Information Theory 69(4) (2023); LATIN (2020), arXiv:1910.02151.
