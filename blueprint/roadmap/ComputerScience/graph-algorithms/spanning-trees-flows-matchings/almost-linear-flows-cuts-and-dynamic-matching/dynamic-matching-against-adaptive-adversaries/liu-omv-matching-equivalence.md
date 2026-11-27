# Liu: sublinear (1+eps)-approximate dynamic vertex cover is equivalent to refuting OMv

There is an online fully dynamic algorithm maintaining a $(1+\varepsilon)$-approximate minimum vertex cover of an $n$-vertex bipartite graph in amortized update time $n^{1-c}\varepsilon^{-C}$, for some constants $c, C > 0$, if and only if the Online Matrix-Vector Multiplication (OMv) conjecture is false. Likewise, a $(1-\varepsilon)$-approximate maximum matching can be maintained in amortized time $n^{1-c}\varepsilon^{-C}$ if and only if a nontrivial algorithm exists for a dynamic approximate OMv problem. Algorithmically, using fast OMv algorithms, a randomized algorithm maintains w.h.p. a $(1-\varepsilon)$-approximate bipartite matching and a $(1+\varepsilon)$-approximate vertex cover in amortized update time $O(\varepsilon^{-O(1)} n / 2^{\Omega(\sqrt{\log n})})$.

## Proof sketch

In one direction, OMv instances are encoded as bipartite graphs whose approximate vertex covers reveal the products, so a fast dynamic cover algorithm would break the conjecture. In the other direction, a multiplicative-weights or augmenting-path framework for approximate matching and its dual cover issues, per phase, a batch of queries that are exactly approximate matrix-vector products against the adjacency matrix. Plugging in subcubic OMv algorithms, such as the Larsen-Williams bound, gives the stated update time.

## Depends on

- [The online matrix-vector multiplication conjecture](../../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-online-matrix-vector-multiplication.md)
- [Fully dynamic alpha-approximate maximum matching and its value version](dynamic-approximate-matching-problem.md)

## Proof depends on

- [Kőnig's theorem for finite bipartite graphs](../../../../../GraphTheory/matchings-and-flows/k-nig-s-theorem/konig-matching-cover.md)

## Sources

- Yang P. Liu, "On Approximate Fully-Dynamic Matching and Online Matrix-Vector Multiplication", FOCS (2024), arXiv:2403.02582.
- Monika Henzinger, Sebastian Krinninger, Danupon Nanongkai, Thatchaphol Saranurak, "Unifying and Strengthening Hardness for Dynamic Problems via the Online Matrix-Vector Multiplication Conjecture", STOC (2015), arXiv:1511.06773.
