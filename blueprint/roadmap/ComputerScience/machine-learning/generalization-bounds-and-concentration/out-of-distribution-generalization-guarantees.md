# Sharp guarantees for out-of-distribution generalization

This node records a research direction: for which families of distribution shift can a learner trained on some environments guarantee small risk on a new one, and what are the optimal trade-offs?

## What would settle it

Define an admissible family of shifts or interventions that constrains the test distribution, and prove matching achievable-risk and impossibility bounds over that family. Unrestricted shifts admit immediate impossibility results, and causal assumptions must be separated from conclusions drawn from observations.

## Status

No cited source poses this question in the form above; it is a research direction motivated by the cited results. This page does not certify the status or novelty of any particular formulation.

Liu et al. survey out-of-distribution generalization, the setting in which the test distribution differs from the training distribution, so that the i.i.d. assumption fails.

This page records a research direction and asserts no theorem or present-status certification.

## Sources

- J. Liu et al., "Towards out-of-distribution generalization: a survey", preprint version 2 (2023), abstract and introduction. <https://arxiv.org/abs/2108.13624>
