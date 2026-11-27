# Sample compression conjecture

Does every binary concept class of VC dimension d admit a sample-compression scheme of size O(d)? This asks whether learnability always has a compact explanation in terms of retained examples.

## What would settle it

Quantify over concept classes and realizable finite labeled samples. Construct compression/reconstruction maps with total size O(d), including the paper's accounting for side information, such that reconstruction agrees with every sample label. Unlimited auxiliary information would trivialize the claim.

## Status

The cited sources pose this as an open question in the versions cited; this page does not certify its present status.

Cai, Gupta, Jiang and Liaw (preprint) state that the sample compression conjecture is a longstanding open problem and give schemes of size O(d^2 log^2 d), resolving the weaker polynomial-size question; the linear-size conjecture of Floyd and Warmuth is not resolved there.

This page records the cited research question and asserts no theorem or present-status certification.

## Sources

- Yang Cai et al., *Near-Quadratic Sample Compression for All VC Classes*, arXiv:2611.25011v1 (2026), abstract and §1. <https://arxiv.org/abs/2611.25011v1>
