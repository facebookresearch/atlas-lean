# Liu: sublinear (1+eps)-approximate dynamic vertex cover is equivalent to refuting OMv

There is a randomized online fully dynamic algorithm maintaining a $(1+\varepsilon)$-approximate minimum vertex cover of an $n$-vertex bipartite graph in amortized update time $n^{1-c}\varepsilon^{-C}$, for some constants $c, C > 0$, if and only if the Online Matrix-Vector Multiplication (OMv) conjecture is false. Likewise (Liu, Theorem 2), a randomized algorithm maintains a $(1-\varepsilon)$-approximate maximum matching against adaptive adversaries in amortized time $n^{1-c}\varepsilon^{-C}$, for some constants $c, C > 0$, if and only if, for some $\delta > 0$, there is an algorithm against adaptive adversaries for dynamic approximate OMv, which maintains a Boolean $n \times n$ matrix $M$ under entry updates and answers each query vector $v$ with a vector within Hamming distance $n^{1-\delta}$ of the Boolean product $Mv$, in amortized time $n^{1-\delta}$ per update and $n^{2-\delta}$ per query. Algorithmically, using fast OMv algorithms, a randomized algorithm maintains w.h.p. a $(1-\varepsilon)$-approximate bipartite matching and a $(1+\varepsilon)$-approximate vertex cover in amortized update time $O(\varepsilon^{-O(1)} n / 2^{\Omega(\sqrt{\log n})})$.

## Proof sketch

In one direction, OMv instances are encoded as bipartite graphs whose approximate vertex covers reveal the products, so a fast dynamic cover algorithm would break the conjecture. In the other direction, a multiplicative-weights or augmenting-path framework for approximate matching and its dual cover issues, per phase, a batch of queries that are exactly approximate matrix-vector products against the adjacency matrix. Plugging in the Larsen-Williams OMv algorithm, which answers each query vector in amortized $n^2/2^{\Omega(\sqrt{\log n})}$ time against adaptive adversaries (a $2^{\Omega(\sqrt{\log n})}$ saving, not a truly subcubic algorithm), gives the stated update time.

## Depends on

- [The online matrix-vector multiplication conjecture](../../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-online-matrix-vector-multiplication.md)
- [Fully dynamic alpha-approximate maximum matching and its value version](dynamic-approximate-matching-problem.md)

## Proof depends on

- [Kőnig's theorem for finite bipartite graphs](../../../../../GraphTheory/matchings-and-flows/k-nig-s-theorem/konig-matching-cover.md)

## Sources

- Yang P. Liu, "On Approximate Fully-Dynamic Matching and Online Matrix-Vector Multiplication", FOCS (2024), arXiv:2403.02582.
- Monika Henzinger, Sebastian Krinninger, Danupon Nanongkai, Thatchaphol Saranurak, "Unifying and Strengthening Hardness for Dynamic Problems via the Online Matrix-Vector Multiplication Conjecture", STOC (2015), arXiv:1511.06773.
- Kasper Green Larsen, Ryan Williams, "Faster Online Matrix-Vector Multiplication", SODA (2017), arXiv:1605.01695.
