# Mohle Sagitov Lambda

The **Möhle–Sagitov conditions for a Λ-coalescent limit** of a sequence of Cannings models
(`M N` has population size `N`), with Λ a finite measure on `[0, 1]`:

* the coalescence probability `c_N` is eventually positive and tends to `0`;
* for every `k ≥ 2`, the probability `q_k` that `k` lineages merge in one generation satisfies
  `q_k / c_N → ∫ x ^ (k - 2) Λ(dx)`; by `mergeProb_mul_descFactorial` this is the offspring
  condition `E[(ν_1)_k] / (N ^ (k - 1) c_N) → ∫ x ^ (k - 2) Λ(dx)` of Möhle–Sagitov (2001);
* simultaneous mergers are negligible: `doubleMergeProb / c_N → 0`, equivalently
  `E[(ν_1)_2 (ν_2)_2] / (N ^ 2 c_N) → 0`.

The limits `φ_k = lim q_k / c_N` are the moments of Λ, so Λ is determined by the model
(`eq_of_mohleSagitovLambda`); `k = 2` forces Λ to be a probability measure.
