# Strings with $\gamma = \Omega(\delta\log(n/\delta))$

For every length $n$ and every integer $\delta$ with $2 \le \delta \le n$ there is a string $T$ of length $n$ with $\delta(T) = \delta$ and $\gamma(T) = \Omega(\delta \log\frac{n}{\delta})$. Hence $\gamma$ is not bounded by $O(\delta)$ uniformly over all strings: whenever $\delta = o(n)$ these strings have $\gamma = \omega(\delta)$, and so does every measure lower-bounded by $\gamma$.

## Proof sketch

Let $S_\infty$ have $\mathtt{b}$ at the positions $2^j$ ($j \ge 0$) and $\mathtt{a}$ elsewhere, and let $S_n$ be its length-$n$ prefix. Beyond position $2^{j-1}$ consecutive $\mathtt{b}$'s are at distance at least $2^j$, so $d_k(S_n) \le 2^{\lceil\log k\rceil - 1} + k + 1 \le 2k$ and $\delta(S_n) \le 2$; each $\mathtt{b}\mathtt{a}^{2^j-1}\mathtt{b}$ occurs only at $[2^j, 2^{j+1}]$, and these regions are disjoint for even $j$, so $\gamma(S_n) \ge \frac12\lfloor\log n\rfloor$. Concatenating $m$ such strings of lengths $\Theta(n/m)$ (and at least $3$) over disjoint alphabets, separated by $m - 1$ distinct delimiters, for $n \ge 4m - 1$, gives $d_k \le (3m-1)k$ and $d_1 = 3m - 1$, so $\delta = 3m - 1$ exactly, while $\gamma = \Omega(m\log(n/m))$. For $\delta < \frac34 n$ not of the form $3m - 1$, take $m = \lfloor (\delta+1)/3 \rfloor$ and append $(\delta + 1) \bmod 3$ further fresh delimiters, which raises $\delta$ by exactly that amount; for $\delta \ge \frac34 n$ the claim reduces to $\gamma = \Omega(\delta)$, which follows from $\delta \le \gamma$ for a string such as $c_1 c_2 \cdots c_\delta\, c_\delta^{\,n-\delta}$ over $\delta$ distinct letters, with $d_k = \min\{\delta, n - k + 1\}$, hence $\delta(T) = \delta$.

## Depends on

- [Substring complexity $\delta$](substring-complexity.md)
- [String attractors](string-attractor.md)

## Proof depends on

- [Substring complexity is at most the attractor size](delta-at-most-gamma.md)

## Sources

- Tomasz Kociumaka, Gonzalo Navarro, Nicola Prezza, "Toward a Definitive Compressibility Measure for Repetitive Sequences", IEEE Transactions on Information Theory 69(4) (2023); LATIN (2020), arXiv:1910.02151.
