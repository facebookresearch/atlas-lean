# Good cuckoo hash-pair contract

Fix a capacity $n$, sub-table size $r$ and eviction cap $L$. A seed distribution for a pair $(h_1, h_2)$ is a *good cuckoo hash pair* with constants $C_{\mathrm{walk}}$ and $C_{\mathrm{reh}}$ if, for every set $S$ of at most $n$ keys and every new key $x$ fixed in advance:

1. the expected number of displacement rounds (iterations of the Pagh–Rodler insertion loop, each moving a key into the first and then the second table) of inserting $x$ into any valid placement of $S$ is at most $C_{\mathrm{walk}}$;
2. the probability that some insertion order of $S$ fails to be placed within $L$ displacements per insertion is at most $1/2$;
3. the probability that inserting $x$ into a valid placement of $S$ exceeds the cap is at most $C_{\mathrm{reh}} / n^2$ (for $n \ge 3$).

## Depends on

- [Cuckoo graph of a key set](cuckoo-graph.md)
- [Placement invariant of a cuckoo hash table](../../cuckoo-hashing/valid.md)
- [Cuckoo eviction loop](../../cuckoo-hashing/insert-aux.md)

## Sources

- R. Pagh and F. F. Rodler, "Cuckoo Hashing", Journal of Algorithms 51(2), 2004 (Section 2.3 bounds exactly these three quantities, for $r \ge (1+\varepsilon)n$ and MaxLoop $= \lceil 3 \log_{1+\varepsilon} r \rceil$: expected iterations $O(1 + 1/\varepsilon)$, rehash probability $O(1/n^2)$ per insertion, and a rehash of all keys succeeding with probability $1 - O(1/n)$; the explicit constants $C_{\mathrm{walk}}$, $C_{\mathrm{reh}}$ and the bound $1/2$ are this page's parametrization).
