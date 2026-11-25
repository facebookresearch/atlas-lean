# Maximum agreement subtree of two random binary trees

Determine the growth exponent of the maximum agreement subtree (MAST) of two independent uniform leaf-labeled binary trees. This supports null models for comparing inferred phylogenies.

## What would settle it

Define restrictions of trees to common leaf sets and MAST as a maximum. Identify β and prove $\log \mathbb{E}[\mathrm{MAST}(T_n, T'_n)] / \log n \to \beta$, or close the current exponent gap. Fix rooted/unrooted and sampling conventions from the source.

## Status

The cited sources pose this as an open question in the versions cited; this page does not certify its present status. The supporting open-problem statement is older or its status evidence is incomplete; check later literature before relying on it.

Budzinski and Sénizergues prove that the maximum agreement subtree is typically smaller than n^{1/2−ε} and that its expectation is at most n^{1/2−ε} for some ε > 0, confirming a conjecture of Aldous that n^{1/2} is not the right order; they record polynomial lower bounds, the best of order n^{0.4464} in expectation. The exponent is not determined there.

This page records the cited research question and asserts no theorem or present-status certification.

## Sources

- Thomas Budzinski and Delphin Sénizergues, *Maximum Agreement Subtrees and Hölder homeomorphisms between Brownian trees*, arXiv:2304.00905v2 (2024), §1, Theorem 1. <https://arxiv.org/abs/2304.00905v2>
