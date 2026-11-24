# Task claim: the kernel of a compact operator on a nonseparable Hilbert space

This temporary note opens the draft pull request that claims the ATLAS task
`af_7f09a35d1c584536ab0f29d9`. It will be removed when the proof lands on this branch.

- Article: `blueprint/roadmap/Analysis/operator-theory/compact-and-fredholm/not-separable-space-ker-of-is-compact-op.md`
- Lean declaration: `MathlibExt.Analysis.OperatorTheory.CompactOperatorKernelNonseparableWanted.not_separableSpace_ker_of_isCompactOperator_of_not_separableSpace`, the only theorem of `WantedExt/Analysis/OperatorTheory/CompactOperatorKernelNonseparableWanted.lean`
- Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II, problem `ma_proofbench_l2_42`.

Statement to prove, with its name and statement unchanged: if $H$ is a complex Hilbert space that is not separable and $A : H \to H$ is a compact
operator, then the kernel of $A$ is not separable.
