# Good cuckoo hash-pair contract

Fix a capacity $n$, sub-table size $r$ and eviction cap $L$. A seed distribution for a pair $(h_1, h_2)$ is a *good cuckoo hash pair* with constants $C_{\mathrm{walk}}$ and $C_{\mathrm{reh}}$ if, for every set $S$ of at most $n$ keys and every new key $x$ fixed in advance:

1. the expected number of displacement rounds of inserting $x$ into any valid placement of $S$ is at most $C_{\mathrm{walk}}$;
2. the probability that some insertion order of $S$ fails to be placed within $L$ displacements per insertion is at most $1/2$;
3. the probability that inserting $x$ into a valid placement of $S$ exceeds the cap is at most $C_{\mathrm{reh}} / n^2$ (for $n \ge 3$).

## Depends on

- [Cuckoo graph of a key set](cuckoo-graph.md)

## Sources

- R. Pagh and F. F. Rodler, "Cuckoo Hashing", Journal of Algorithms 51(2), 2004.
