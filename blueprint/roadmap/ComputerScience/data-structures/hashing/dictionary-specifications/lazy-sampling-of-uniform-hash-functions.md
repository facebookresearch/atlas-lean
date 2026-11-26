# Lazy sampling of uniform hash functions

Let a client interact with a uniformly random function $F : X \to Y$ ($X$ finite, $Y$ finite and nonempty), i.e. with $F$ drawn uniformly from $Y^X$ before the interaction. Then the joint distribution of the client's queries and answers equals that obtained by *lazy sampling*: answer the first query at each point $x$ with a fresh uniform element of $Y$, record it, and answer repeated queries at $x$ consistently. In particular the uniform-hashing model, in which every key has an independent uniform random probe permutation, may be analysed with permutations drawn on demand.

## Proof sketch

Under a uniform $F$, conditioned on the answers so far, the values at unqueried points remain independent and uniform. Induct on the number of queries, comparing the conditional law of the next answer in both processes.

## Depends on

- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)

## Sources

- M. Mitzenmacher and E. Upfal, "Probability and Computing", 2nd edition, Cambridge University Press, 2017.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
