# Variance of the longest common subsequence of random binary words

Determine the asymptotic variance of the longest common subsequence (LCS) of two independent, uniformly random binary words of length n. This is a foundational null-model question for alignment statistics, not a claim about real genomes. A linear upper bound is known; a matching linear lower bound in the uniform binary case remains the target in the cited work.

## What would settle it

Define LCS by finite optimization and L_n on the uniform space of 4^n word pairs. The linear-variance conjecture becomes $\exists c > 0\, \exists n_0\, \forall n \ge n_0,\ \mathrm{Var}(L_n) \ge c n$. Proving a different asymptotic order would also resolve the question, but merely checking many n would not.

## Status

The cited sources pose this as an open question in the versions cited; this page does not certify its present status. The supporting open-problem statement is older or its status evidence is incomplete; check later literature before relying on it.

Houdré and Işlak (§1) record Steele's linear upper bound on the variance and state that the order of a matching lower bound remains unknown for independent uniform binary letters; both sublinear and linear conjectures have appeared in the literature they cite.

This page records the cited research question and asserts no theorem or present-status certification.

## Sources

- Christian Houdré and Ümit Işlak, *A Central Limit Theorem for the Length of the Longest Common Subsequences in Random Words*, arXiv:1408.1559v6 (2023), §1. <https://arxiv.org/abs/1408.1559v6>
