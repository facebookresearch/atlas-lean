# Strings are representable in $O(\delta\log(n/\delta))$ space, optimally

Every string $T$ of length $n$ with substring complexity $\delta$ can be represented in $O(\delta \log\frac{n}{\delta})$ machine words with access to any position in $O(\log\frac{n}{\delta})$ time, and with indexing support for pattern matching in the same asymptotic space. The space is worst-case optimal as a function of $n$ and $\delta$ over alphabets of size polynomial in $n$: for all $n$ and $\delta$ there are such families of strings with substring complexity at most $\delta$ that require $\Omega(\delta\log\frac{n}{\delta})$ words, i.e. $\Omega(\delta \log\frac{n}{\delta} \log n)$ bits, to distinguish (for an alphabet of size $\sigma$ the optimum is $\Theta(\delta\log\frac{n\log\sigma}{\delta\log n})$ words).

## Proof sketch

Kociumaka, Navarro and Prezza show that a block tree has $O(\delta)$ marked blocks per level: each position of a marked block of length $\tau^k$ is the centre of a distinct substring of length $4\tau^k$ (after padding), so there are at most $d_{4\tau^k}/\tau^k + 4 \le 4\delta + 4$ of them; with constant $\tau$ and $O(\log(n/\delta))$ levels this gives $O(\delta\log(n/\delta))$ words and $O(\log(n/\delta))$ access (also $z = O(\delta\log(n/\delta))$ by a bound of Raskhodnikova et al.). Indexing uses a run-length grammar of size $O(\delta\log(n/\delta))$ with the grammar-based index of Christiansen et al. The lower bound is a counting argument: an explicit family of length-$n$ strings of common measure $\delta$ needs $\Omega(\delta\log(n/\delta)\log n)$ bits.

## Depends on

- [Substring complexity $\delta$](substring-complexity.md)

## Sources

- Tomasz Kociumaka, Gonzalo Navarro, Nicola Prezza, "Toward a Definitive Compressibility Measure for Repetitive Sequences", IEEE Transactions on Information Theory 69(4) (2023); LATIN (2020), arXiv:1910.02151.
- Anders Roy Christiansen, Mikko Berggren Ettienne, Tomasz Kociumaka, Gonzalo Navarro, Nicola Prezza, "Optimal-Time Dictionary-Compressed Indexes", ACM Transactions on Algorithms 17(1) (2021), arXiv:1811.12779.
