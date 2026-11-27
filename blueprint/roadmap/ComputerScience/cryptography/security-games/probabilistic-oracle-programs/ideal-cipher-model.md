# Ideal cipher model

Let $K$ be a finite key set and $X$ a finite nonempty block set. The *ideal cipher* on $(K, X)$ is a family $\Pi = (\Pi_k)_{k \in K}$ of independent uniformly random permutations of $X$. An adversary in the ideal cipher model is a probabilistic oracle program with two kinds of queries: forward queries $(k, x)$ answered by $\Pi_k(x)$, and inverse queries $(k, y)$ answered by $\Pi_k^{-1}(y)$. The ideal cipher can be sampled *lazily*: each answer to a fresh query is drawn uniformly from the values not yet used by the partial permutation for that key, which induces exactly the same distribution on transcripts as sampling all permutations in advance.

## Depends on

- [Probabilistic oracle program and its semantics against a stateful handler](probabilistic-oracle-program.md)
- [Lazy random permutation](../lazy-sampling-and-the-prp-prf-switching-lemma/lazy-rp.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- J. Black, P. Rogaway and T. Shrimpton, "Black-Box Analysis of the Block-Cipher-Based Hash-Function Constructions from PGV", Advances in Cryptology (CRYPTO 2002), LNCS 2442, 2002.
