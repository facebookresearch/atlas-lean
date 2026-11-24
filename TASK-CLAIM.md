# Task claim: closed form of the series of sin²(nδ)/(n²δ)

This temporary note opens the draft pull request that claims the ATLAS task
`af_198e6344275a2c6e3f290466`. It will be removed when the proof lands on this branch.

- Article: `blueprint/roadmap/Analysis/sequences-and-series/trigonometric-and-harmonic-series/tsum-sin-sq-mul-div-sq-mul.md`
- Lean declaration: `MathlibExt.Analysis.SpecificLimits.SumSinSqDivSqWanted.tsum_sin_sq_mul_div_sq_mul`,
  a `theorem_wanted` in `WantedExt/Analysis/SpecificLimits/SumSinSqDivSqWanted.lean`
- Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I, problem `ma_proofbench_l1_03`.

Statement to prove, with its name and statement unchanged: for every real $\delta$ with
$0 < \delta < \pi$,

$$\sum_{n=1}^{\infty} \frac{\sin^2(n\delta)}{n^2\delta} = \frac{\pi - \delta}{2}.$$
