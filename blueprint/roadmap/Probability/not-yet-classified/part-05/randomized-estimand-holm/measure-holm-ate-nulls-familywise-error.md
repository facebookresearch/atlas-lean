# Holm controls the FWER over the causal nulls

Under strong ignorability given `X` of
every endpoint with zero average treatment effect (nothing is assumed about the others), with
p-values calibrated for the observed-data IPW null and no assumption on their dependence, the
probability that Holm's step-down procedure at level `α ∈ [0, 1]` rejects some endpoint with zero
average treatment effect is at most `α`. The merged `measure_holm_familywiseError_le` is applied
to the causal nulls via `isValidPValue_of_mem_ateNulls`. No power claim is made.

## Sources

- Holm (1979); identification as in Rosenbaum & Rubin (1983).
