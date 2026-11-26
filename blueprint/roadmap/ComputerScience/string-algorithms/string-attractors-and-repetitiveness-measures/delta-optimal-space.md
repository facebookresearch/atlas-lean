# Strings are representable in $O(\delta\log(n/\delta))$ space, optimally

Every string $T$ of length $n$ with substring complexity $\delta$ can be represented in $O(\delta \log\frac{n}{\delta})$ machine words with access to any position in $O(\log\frac{n}{\delta})$ time, and with indexing support for pattern matching in the same asymptotic space. The space is worst-case optimal as a function of $n$ and $\delta$: for all $n$ and $\delta$ there are families of strings with substring complexity at most $\delta$ that require $\Omega(\delta\log\frac{n}{\delta})$ words, i.e. $\Omega(\delta \log\frac{n}{\delta} \log n)$ bits, to distinguish.

## Proof sketch

Kociumaka, Navarro and Prezza construct a block tree whose levels are adapted to $\delta$ rather than to an attractor, using the bound $d_k \le k\delta$ to show that each level has $O(\delta)$ distinct blocks times a geometric factor, which sums to $O(\delta\log(n/\delta))$. The lower bound is a counting argument: an explicit family of length-$n$ strings, all with substring complexity at most $\delta$, has $2^{\Omega(\delta\log(n/\delta)\log n)}$ members, so some member needs that many bits.

## Depends on

- [Substring complexity $\delta$](substring-complexity.md)

## Proof depends on

- [Substring complexity is at most the attractor size](delta-at-most-gamma.md)
- [Universal compressed representations from string attractors](attractor-universal-index.md)

## Sources

- Tomasz Kociumaka, Gonzalo Navarro, Nicola Prezza, "Toward a Definitive Compressibility Measure for Repetitive Sequences", IEEE Transactions on Information Theory 69(4) (2023); LATIN (2020), arXiv:1910.02151.
