# Random access in $\delta$-optimal compressed space

Every string $T$ of length $n$ over an alphabet of size $\sigma$ with substring complexity $\delta$ can be stored in $O\!\left(\delta\log\frac{n\log\sigma}{\delta\log n}\right)$ machine words with efficient random access to its characters, and this is the asymptotically smallest space needed to represent strings, for all combinations of $n$, $\sigma$ and $\delta$.

## Proof sketch

Refine the $\delta$-adapted block tree by stopping the recursion once blocks have length $\Theta(\log_\sigma n)$, at which point they are stored packed in words; this replaces $\log(n/\delta)$ by $\log\frac{n\log\sigma}{\delta\log n}$. The matching lower bound is a counting argument over strings with prescribed substring complexity, generalizing the one for the $O(\delta\log(n/\delta))$ bound to account for the alphabet.

## Depends on

- [Substring complexity $\delta$](../string-attractors-and-repetitiveness-measures/substring-complexity.md)

## Proof depends on

- [Strings are representable in $O(\delta\log(n/\delta))$ space, optimally](../string-attractors-and-repetitiveness-measures/delta-optimal-space.md)

## Sources

- Tomasz Kociumaka, Gonzalo Navarro, Nicola Prezza, "Toward a Definitive Compressibility Measure for Repetitive Sequences", IEEE Transactions on Information Theory 69(4) (2023); LATIN (2020), arXiv:1910.02151.
- Dominik Kempa, Tomasz Kociumaka, "Collapsing the Hierarchy of Compressed Data Structures: Suffix Arrays in Optimal Compressed Space", FOCS (2023), arXiv:2308.03635.
