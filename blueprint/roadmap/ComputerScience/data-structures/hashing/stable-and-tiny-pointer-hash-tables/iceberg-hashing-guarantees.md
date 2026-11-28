# Iceberg hashing: constant time, stability, high load and near-optimal space

Iceberg hashing is a dynamic hash table that, for keys of $\Theta(\log n)$ bits (so $|U| = n^{O(1)}$), supports insertions, deletions and queries in $O(1)$ time each with probability $1 - 1/\mathrm{poly}(n)$, is stable, supports load factors up to $1 - o(1)$, and uses $\log_2 \binom{|U|}{n} + O(n \log\log n)$ bits to store $n$ keys. The $O(n \log \log n)$ redundancy matches a lower bound of Demaine, Meyer auf der Heide, Pagh and Pătraşcu that applies to every stable hash table.

## Proof sketch

The front yard uses bins of size $h = \Theta(\log n)$ whose contents are stored with quotienting, so each key costs $\log_2(|U|/n) + O(1)$ bits plus $O(\log \log n)$ bits of in-bin addressing metadata, giving $O(n\log\log n)$ total redundancy. The overflow lemma keeps the back yard at $o(n)$ keys, where a conventional constant-time table can afford more space. Stability holds because keys never move: a key that overflows to the back yard stays there, and the Iceberg Lemma shows that such an unmanaged back yard still holds at most $n/\mathrm{poly}(h)$ keys at every time, with probability $1 - 2^{-n/\mathrm{polylog}\, n}$, against an oblivious sequence of operations. *Waterfall addressing* performs resizes without an indirection layer.

## Depends on

- [Information-theoretic space bound and redundancy of a dictionary](information-theoretic-space-and-redundancy.md)
- [Stable hash tables](stable-hash-table.md)

## Proof depends on

- [Chernoff bound on front-yard overflow](front-yard-overflow-bound.md)
- [Front-yard and back-yard hash table design](front-yard-back-yard-paradigm.md)

## Sources

- Michael A. Bender, Alex Conway, Martín Farach-Colton, William Kuszmaul, Guido Tagliavini, "Iceberg Hashing: Optimizing Many Hash-Table Criteria at Once", Journal of the ACM 70(6) (2023), arXiv:2109.04548.
- Erik D. Demaine, Friedhelm Meyer auf der Heide, Rasmus Pagh, Mihai Pătraşcu, "De Dictionariis Dynamicis Pauco Spatio Utentibus", LATIN (2006).
