# Task claim: convolution of two square-integrable functions

This temporary note opens the draft pull request that claims the ATLAS task
`af_665340b788e4f3ce19c688e4`. It will be removed when the proof lands on this branch.

- Article: `blueprint/roadmap/Analysis/harmonic-analysis/fourier-transform/continuous-and-tendsto-cocompact-convolu.md`
- Lean declaration: `MathlibExt.Analysis.Fourier.L2ConvolutionContinuousVanishingWanted.continuous_and_tendsto_cocompact_convolution_of_memLp_two`, the only theorem of `WantedExt/Analysis/Fourier/L2ConvolutionContinuousVanishingWanted.lean`
- Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II, problem `ma_proofbench_l2_17`.

Statement to prove, with its name and statement unchanged: for square-integrable $f, g : \mathbb{R}^n \to \mathbb{C}$, the convolution
$x \mapsto \int f(x - y) g(y) \, dy$ is continuous and tends to $0$ at infinity.
