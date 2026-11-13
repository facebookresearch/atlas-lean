# Storey-BH controls the FDR at level `q` under independence

**Storey-BH controls the FDR at level `q` under independence** (Storey, Taylor and Siegmund
2004, Theorem 3). Let `H0` be the set of true nulls. Assume

* every true-null p-value `p i` is valid (super-uniform: `μ {p i ≤ t} ≤ t` for `t ∈ [0, 1]`);
* every true-null p-value `p i` is independent of the vector of all other p-values
  `(p j)_{j ≠ i}` (implied by mutual independence, `iIndepFun`; the false-null p-values may be
  arbitrarily dependent among themselves);
* the tuning parameter `lam ∈ [0, 1)` is fixed, i.e. chosen without looking at the data.

Then BH run at the adaptive level `q / π̂₀(lam)`, with Storey's estimator
`π̂₀(lam) = (#{p j > lam} + 1) / ((1 - lam) m)` and thresholds capped at `lam`
(`storeyBHRejections`), has false discovery rate at most `q`, for every `q ≥ 0`.

Unlike plain BH (`E[FDP] ≤ q |H0| / m`), the bound does not shrink with `|H0| / m`: the adaptive
level spends the slack. The proof goes through the interaction of the adaptive threshold with the
p-values, not through `E[π̂₀] ≥ |H0| / m` (which holds, `TwoGroupsTesting.le_integral_storeyPi0`
and `le_integral_storeyPi0Plus1`, but does not suffice). On `{i rejected}` we have `p i ≤ lam`,
so `π̂₀` does not depend on `p i` and the
leave-one-out property (`storeyBH_leave_one_out`) gives
`E[1{i ∈ R} / |R|] ≤ q (1 - lam) E[1 / (N_i + 1)]`, where `N_i` counts the *other* p-values above
`lam`; then `∑_{i ∈ H0} (1 - lam) E[1 / (N_i + 1)] ≤ 1`
(`sum_integral_inv_storeyPi0Plus1_update_le`). (For `m = 0` both sides are `0`.)

## Sources

- J. D. Storey, J. E. Taylor and D. Siegmund, *Strong control, conservative point estimation and simultaneous conservative consistency of false discovery rates: a unified approach*, J. R. Statist. Soc. B 66 (2004), 187–205, Theorem 3; the leave-one-out argument follows G. Blanchard and É. Roquain, *Adaptive false discovery rate control under independence and dependence*, J. Mach. Learn. Res. 10 (2009), 2837–2871.
