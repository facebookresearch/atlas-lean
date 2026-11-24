# Tightness in `D([0,1])` of martingale difference arrays

Let row `n` of `ξ` be a
square-integrable martingale difference sequence for `𝓕 n` whose predictable quadratic
variation converges in probability to the identity at every `t ∈ [0,1]`, and let `ξ` satisfy
the Lindeberg condition. Then the laws of the step processes `arrayStepProcess n ξ` are tight
in `D([0,1])` with the J1 topology.

## Sources

- Jacod–Shiryaev (2003), Theorem VI.4.13 (Rebolledo: the quadratic-variation condition gives Aldous's condition) with Theorem VI.4.5. Proof: `aldousCondition_of_martingaleDifference` and `tendsto_measure_exists_abs_gt_of_lindeberg` discharge the hypotheses of `isTightMeasureSet_arrayStepProcess_of_aldousCondition`.
