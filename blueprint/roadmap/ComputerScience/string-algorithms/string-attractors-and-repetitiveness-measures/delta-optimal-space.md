# Strings are representable in $O(\delta\log(n/\delta))$ space, optimally

Every string $T$ of length $n$ with substring complexity $\delta$ can be represented in $O(\delta \log\frac{n}{\delta})$ machine words with access to any position in $O(\log\frac{n}{\delta})$ time, and with indexing support for pattern matching in the same asymptotic space. The space is worst-case optimal as a function of $n$ and $\delta$: for every length $n$ and every integer $\delta$ with $2 \le \delta \le n$ there is a family of length-$n$ strings, over alphabets of size at most $n$, all with substring complexity exactly $\delta$, whose members need $\Omega(\delta\log\frac{n}{\delta} \log n)$ bits, i.e. $\Omega(\delta \log\frac{n}{\delta})$ words, to be encoded. The case $\delta = 1$ is excluded because $\delta(T) = 1$ forces $T$ to be a power of a single letter. The journal version further refines the bounds to account for the alphabet size $\sigma$: $\Theta(\delta\log\frac{n\log\sigma}{\delta\log n})$ words are necessary and sufficient to represent the string and to support access and pattern searches.

## Proof sketch

Kociumaka, Navarro and Prezza show that a block tree has $O(\delta)$ marked blocks per level: each position of a marked block of length $\tau^k$ is the centre of a distinct substring of length $4\tau^k$ (after padding), so there are at most $d_{4\tau^k}/\tau^k + 4 \le 4\delta + 4$ of them; with constant $\tau$ and $O(\log(n/\delta))$ levels this gives $O(\delta\log(n/\delta))$ words and $O(\log(n/\delta))$ access (also $z = O(\delta\log(n/\delta))$ by a bound of Raskhodnikova et al.). Indexing uses a run-length grammar of size $O(\delta\log(n/\delta))$ with the grammar-based index of Christiansen et al. The lower bound is a counting argument: an explicit family of length-$n$ strings of common measure $\delta$ needs $\Omega(\delta\log(n/\delta)\log n)$ bits.

## Depends on

- [Substring complexity $\delta$](substring-complexity.md)

## Sources

- Tomasz Kociumaka, Gonzalo Navarro, Nicola Prezza, "Toward a Definitive Compressibility Measure for Repetitive Sequences", IEEE Transactions on Information Theory 69(4) (2023); LATIN (2020), arXiv:1910.02151.
- Anders Roy Christiansen, Mikko Berggren Ettienne, Tomasz Kociumaka, Gonzalo Navarro, Nicola Prezza, "Optimal-Time Dictionary-Compressed Indexes", ACM Transactions on Algorithms 17(1) (2021), arXiv:1811.12779.
