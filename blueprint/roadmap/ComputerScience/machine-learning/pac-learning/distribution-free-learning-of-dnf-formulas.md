# Distribution-free PAC learning of DNF formulas

Can arbitrary polynomial-size disjunctive-normal-form rules be PAC learned efficiently from random labeled examples under any input distribution?

## What would settle it

Construct a learner with running time and sample count polynomial in dimension, target size, inverse error, and the relevant confidence parameter, and prove its PAC guarantee for every distribution. Specify examples-only versus membership-query access and proper versus improper output.

## Status

The cited sources pose this as an open question in the versions cited; this page does not certify its present status.

Alman, Nadimpalli, Patel and Servedio describe progress on the distribution-free problem as limited and record that the fastest known algorithms take time n^{O(s)} for small s and 2^{Õ(n^{1/3})} in general; their own results use membership queries.

This page records the cited research question and asserts no theorem or present-status certification.

## Sources

- Josh Alman et al., *DNF Learning via Locally Mixing Random Walks*, arXiv:2505.18839v1 (2025), §1.1. <https://arxiv.org/abs/2505.18839v1>
