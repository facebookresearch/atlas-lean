# Approximation ratio of the greedy superstring algorithm

Determine the approximation ratio of the greedy shortest-superstring algorithm: repeatedly merge strings with maximum overlap. This is an idealized assembly question, not a guarantee for a modern genome assembler.

## What would settle it

State strings, overlap, substring preprocessing, and tie-breaking. Define the supremum of $|\mathrm{greedy}(S)| / |\mathrm{opt}(S)|$ over nonempty instances and permitted executions. Prove a sharper universal upper bound or a matching family of lower-bound instances.

## Status

The cited sources pose this as an open question in the versions cited; this page does not certify its present status.

Chukhin, Gajjala, Harviainen and Kulikov (preprint) refute the classical conjecture that the greedy ratio is 2: they construct instances whose ratio tends to 2.4 and prove that the greedy algorithm is 3-approximate. Another algorithm with a better ratio would not determine the ratio of the greedy algorithm itself.

This page records the cited research question and asserts no theorem or present-status certification.

## Sources

- Nikolai Chukhin et al., *The Greedy Superstring Conjecture Is False*, arXiv:2609.01365v2 (2026), abstract and §1. <https://arxiv.org/abs/2609.01365v2>
