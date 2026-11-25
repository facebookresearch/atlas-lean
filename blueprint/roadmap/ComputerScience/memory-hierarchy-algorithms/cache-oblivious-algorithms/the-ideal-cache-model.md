# The ideal-cache model

The $(Z, L)$ ideal-cache model is a computer with a two-level memory hierarchy: a cache of $Z$ words and an arbitrarily large main memory, with words of a constant size. The cache is partitioned into cache lines of $L$ consecutive words, which are always moved together between cache and main memory. The processor can reference only words that reside in the cache: if the referenced word belongs to a line already in the cache, a *cache hit* occurs; otherwise a *cache miss* occurs and the line is fetched into the cache. The cache is fully associative, so a line can be stored anywhere in it, and when the cache is full it evicts the line whose next access is furthest in the future (the optimal offline replacement strategy).

An algorithm with an input of size $n$ is measured by its *work* $W(n)$, its running time in a RAM model, and by its *cache complexity* $Q(n; Z, L)$, the number of cache misses it incurs. The cache is *tall* if $Z = \Omega(L^2)$. An algorithm is *cache aware* if it contains parameters, set at compile time or at run time, that can be tuned to optimize its cache complexity for a particular cache size and line length; otherwise it is *cache oblivious*.

## Sources

- M. Frigo, C. E. Leiserson, H. Prokop and S. Ramachandran, "Cache-oblivious algorithms", *Proceedings of the 40th IEEE FOCS*, 1999, Section 1 and Figure 1
