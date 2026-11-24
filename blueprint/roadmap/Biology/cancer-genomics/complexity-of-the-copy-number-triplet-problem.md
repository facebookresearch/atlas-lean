# Complexity of the copy-number triplet problem

Given two copy-number profiles, find a common ancestral profile minimizing the total directed event cost to both descendants. This is a building block of tumor copy-number phylogenetics.

## What would settle it

Preserve the source's segment-event costs and zero-copy restrictions. Prove a polynomial-time exact algorithm in the binary encoding length, or an appropriate hardness reduction. A pseudo-polynomial algorithm already exists; merely being polynomial in the largest copy number is not a solution.

## Status

The cited sources pose this as an open question in the versions cited; this page does not certify its present status. The supporting open-problem statement is older or its status evidence is incomplete; check later literature before relying on it.

El-Kebir et al. give a pseudo-polynomial algorithm and an integer linear program for CN3 and state in their conclusions that its computational complexity remains open.

This page records the cited research question and asserts no theorem or present-status certification.

## Sources

- M. El-Kebir et al., *Complexity and algorithms for copy-number evolution problems*, Algorithms for Molecular Biology 12 (2017), conclusions. <https://pmc.ncbi.nlm.nih.gov/articles/PMC5433102/>
