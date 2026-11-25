# Information requirements for CRISPR lineage tracing

This node records a research direction: how many independent recording sites are necessary, not merely sufficient, to recover a lineage tree under the mutation and dropout model of CRISPR-based lineage tracing?

## What would settle it

In the generative model of the cited paper, with the tree-height normalization, minimum edge length, mutation rate, state space and missing-data model fixed, prove a lower bound on the number of sites that holds for every estimator and matches the sufficient bound up to constants, or give an algorithm improving the sufficient bound.

## Status

No cited source poses this question in the form above; it is a research direction motivated by the cited results. This page does not certify the status or novelty of any particular formulation.

Wang, Zhang, Khodaverdian and Yosef prove (Theorem 1 and Corollary 1) that, for a tree of height normalized to 1 with n leaves, minimum edge length ℓ with λℓ ≤ 1, and constant mutation rate and state space, a polynomial-time algorithm recovers the tree exactly with high probability from k = O(log n / ℓ²) sites, without dropout, and a related bound for well-separated triplets without a minimum edge length (Theorem 2).

This page records a research direction and asserts no theorem or present-status certification.

## Sources

- R. Wang, R. Zhang, A. Khodaverdian and N. Yosef, "Theoretical guarantees for phylogeny inference from single-cell lineage tracing", Proceedings of the National Academy of Sciences USA 120 (2023), e2203352120, Theorems 1 and 2 and Corollary 1. <https://doi.org/10.1073/pnas.2203352120>
