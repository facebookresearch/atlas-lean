# Donsker's invariance principle in the Skorokhod space `D((0,1))`

**Donsker's invariance principle in the Skorokhod space `D([0,1])`** for the normalized
partial-sum step process `t ↦ (√n)⁻¹ ∑_{i < ⌊n t⌋} X i` of an i.i.d. mean-zero, variance-one
sequence: it converges in distribution, in the Skorokhod J1 topology, to a continuous version
of Brownian motion on `[0,1]`.

This is the martingale functional CLT restricted to square-integrable martingales with
i.i.d. increments, obtained by discharging the three inputs of
`tendstoInDistribution_skorokhod_of_tight_of_fdd` with `Y n` Donsker's polygonal process:
* tightness: `isTightMeasureSet_donskerProcess_laws` (from Donsker convergence via Prokhorov's
  converse);
* finite-dimensional convergence: continuous mapping applied to `donsker_invariance_principle`;
* jump control: `sup_t |step - polygon| ≤ max_{i<n} |X i| / √n`, which tends to `0` in
  probability (proved here from the second moment of `X 0`).
Mathematically the step process is a martingale in `k = ⌊n t⌋` with deterministic predictable
quadratic variation `⌊n t⌋ / n → t`; those facts are formalized only for the Bernoulli
example (`martingale_compensatedBernoulli`, `condExp_sq_increment_compensatedBernoulli`).

## Sources

- Billingsley (1999), Theorem 16.1 (Donsker in `D`); proof route: Donsker in `C` (Theorem 8.2, here `donsker_invariance_principle`), sup-distance comparison of the step and polygonal processes, and converging together (Theorem 3.1).
