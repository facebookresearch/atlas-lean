---
article_id: af_a6f69cc9c6754a0f115b842e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: LovaszLocalLemma.lovasz_local_lemma_rv
---

# Theorem 1.1.8 (Lovász local lemma – random variable model)

Let $x_1, \ldots, x_N$ be independent random variables. Let $B_1, \ldots, B_m \subseteq [N]$. For each $i$, let $E_i$ be an event that depends only on the variables indexed by $B_i$ (i.e., $E_i$ is allowed to depend only on $\{x_j : j \in B_i\}$). Suppose, for every $i \in [m]$, $B_i$ has non-empty intersections with at most $d$ other $B_j$'s, and $\mathbb{P}[E_i] \leq \frac{1}{(d+1)e}$. Then with positive probability, none of the events $E_i$ occur.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Corollary 6.5.2 (Lopsided local lemma; symmetric version)](../chapter-6/chapter-6-section-6-5/098-lopsided-local-lemma-symmetric-version.md)

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Chapter 1, Section 1.1](../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)
