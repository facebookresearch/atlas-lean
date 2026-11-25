# Expected probes in open addressing

In an open-address hash table with load factor $\alpha = n/m < 1$ built by $n$ insertions and no deletions, under uniform hashing (each key's probe sequence is a uniformly random permutation of the $m$ slots, independently of other keys), the expected number of probes in an unsuccessful search is at most $1/(1 - \alpha)$, and in a successful search for a uniformly chosen stored key at most $\frac{1}{\alpha} \ln \frac{1}{1 - \alpha}$.

## Expansion

This page becomes ready once:

- Dictionary and ordered-set abstract data types (statement prerequisite; formal statement exists, page pending)
- The two probe bounds must be checked against the cited texts, which have not been opened

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*, 4th ed., MIT Press, 2022
- D. E. Knuth, *The Art of Computer Programming*, vol. 3: Sorting and Searching, 2nd ed., Addison-Wesley, 1998
