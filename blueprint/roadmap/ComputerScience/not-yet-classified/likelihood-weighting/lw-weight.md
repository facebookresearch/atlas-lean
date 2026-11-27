# Lw Weight

The **likelihood weight** of an assignment `x` of a Bayesian network over a nonempty alphabet for evidence nodes `E`: the product of the
tables of the evidence nodes at `x`, `∏_{k ∈ E} p_k (x_k | x_{pa k})`. On assignments that agree
with the evidence this is the likelihood of the evidence given the sampled non-evidence values.
