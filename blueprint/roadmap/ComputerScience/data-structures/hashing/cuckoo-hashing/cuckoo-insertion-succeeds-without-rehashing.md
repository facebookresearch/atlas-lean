# Cuckoo insertion succeeds without rehashing with high probability

Fix $\varepsilon > 0$. In cuckoo hashing with two tables of $\lceil (1 + \varepsilon) n \rceil$ cells each and two independent fully random hash functions, every key is stored in one of its two possible locations, so a lookup probes at most two cells. Inserting $n$ keys by the cuckoo eviction procedure, which moves keys along a path of evictions without a bound on its length, and which fails to terminate exactly when the key's component of the cuckoo graph has more than one cycle, succeeds without a rehash with probability $1 - O(1/n)$, by the analysis of the random cuckoo graph whose vertices are cells and whose edges are keys: a sequence of insertions fails only if some connected component of that graph contains more than one cycle (a walk around the unique cycle of a unicyclic component revisits keys and still terminates).

## Expansion

This page becomes ready once:

- Dictionary and ordered-set abstract data types (statement prerequisite; formal statement exists, page pending)

## Sources

- R. Pagh and F. F. Rodler, "Cuckoo hashing", *Journal of Algorithms* 51(2):122–144, 2004
- A. Gupta, *Advanced Algorithms*, lecture notes for CMU 15-850, Fall 2020, <https://www.cs.cmu.edu/~15850/notes/cmu850-f20.pdf>
