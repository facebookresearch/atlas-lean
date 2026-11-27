# Random access in $\delta$-optimal compressed space

Every string $T$ of length $n$ over an alphabet of size $\sigma \le n^{O(1)}$ with substring complexity $\delta$ can be stored in a block tree of $O\!\left(\delta\log\frac{n\log\sigma}{\delta\log n}\right)$ machine words of $\Theta(\log n)$ bits from which any substring of length $\ell$ is extracted in $O\!\left(\lceil \ell/\log_\sigma n\rceil \log\frac{n\log\sigma}{\delta\log n}\right)$ time. This space is worst-case optimal on hard families: there is an absolute constant $\beta > 0$ such that for every length $n$, alphabet size $\sigma$ and value $\Delta$ with $14\sigma \le \Delta \le \frac{n}{2}\cdot\frac{\log\sigma}{\log n}$ there is a family of length-$n$ strings over an alphabet of size $\sigma$, all with $\delta \le \Delta$, some member of which needs $\beta\,\Delta\log\frac{n\log\sigma}{\Delta\log n}\cdot\log n$ bits to be encoded. The lower bound is not claimed for every $\delta$: a string with $\delta = 1$ is a run of a single symbol, which needs only $O(\log n + \log\sigma)$ bits.

## Proof sketch

Refine the $\delta$-adapted block tree by stopping the recursion once blocks have length $\Theta(\log_\sigma n)$, at which point they are stored packed in words; this replaces $\log(n/\delta)$ by $\log\frac{n\log\sigma}{\delta\log n}$. The matching lower bound is a counting argument over strings with prescribed substring complexity, generalizing the one for the $O(\delta\log(n/\delta))$ bound to account for the alphabet.

## Depends on

- [Substring complexity $\delta$](../string-attractors-and-repetitiveness-measures/substring-complexity.md)

## Proof depends on

- [Strings are representable in $O(\delta\log(n/\delta))$ space, optimally](../string-attractors-and-repetitiveness-measures/delta-optimal-space.md)

## Sources

- Tomasz Kociumaka, Gonzalo Navarro, Nicola Prezza, "Toward a Definitive Compressibility Measure for Repetitive Sequences", IEEE Transactions on Information Theory 69(4) (2023), Theorem IV.8 and Corollary VI.7; LATIN (2020), arXiv:1910.02151.
- Dominik Kempa, Tomasz Kociumaka, "Collapsing the Hierarchy of Compressed Data Structures: Suffix Arrays in Optimal Compressed Space", FOCS (2023), arXiv:2308.03635.
