# Limits of cache-obliviousness: tall caches are necessary for optimal sorting

No cache-oblivious comparison-based sorting algorithm is I/O-optimal for all cache parameters without a tall-cache assumption: there is an inherent tradeoff between the strength $\varepsilon$ of a tall-cache assumption $Z \ge L^{1+\varepsilon}$ and the I/O overhead incurred when $Z \gg L$, and funnelsort and recursive binary mergesort are optimal points of this tradeoff. Moreover, there is no I/O-optimal cache-oblivious algorithm for permuting, even under a tall-cache assumption.

## Proof sketch

Brodal and Fagerberg run a fixed cache-oblivious algorithm against two cache configurations with different line lengths and bound, by an information-theoretic count of the comparison outcomes that the I/Os of each configuration can make available, how the algorithm's work must be split between them; optimality in both configurations forces a relation between $Z$ and $L$ of tall-cache type, with the overhead growing as $\varepsilon \to 0$. For permuting, optimality would require choosing obliviously between the two branches $N$ and $\frac{N}{L}\log_{Z/L}\frac{N}{L}$ of the permuting bound, which a single algorithm cannot do for all parameters.

## Depends on

- [Tall-cache assumptions](tall-cache-assumption.md)
- [Funnelsort](../cache-oblivious-algorithms/funnelsort.md)
- [The ideal-cache model](../cache-oblivious-algorithms/the-ideal-cache-model.md)

## Proof depends on

- [Cache-complexity lower bound for sorting](../cache-oblivious-algorithms/cache-complexity-lower-bound-for-sorting.md)
- [I/O complexity of permuting](../external-memory-algorithms/i-o-complexity-of-permuting.md)

## Sources

- Gerth Stølting Brodal, Rolf Fagerberg, "On the Limits of Cache-Obliviousness", STOC (2003).
- Gerth Stølting Brodal, Rolf Fagerberg, "Cache Oblivious Distribution Sweeping", ICALP (2002).
