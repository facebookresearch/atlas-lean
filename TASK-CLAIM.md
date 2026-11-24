# Task claim: strong operator convergence characterized by weak operator convergence

This temporary note opens the draft pull request that claims the ATLAS task
`af_75958b7dd706958a0ff01a5c`. It will be removed when the proof lands on this branch.

- Article: `blueprint/roadmap/Analysis/operator-theory/bounded-operators/tendsto-apply-iff-tendsto-inner-and-tend.md`
- Lean declaration:
  `MathlibExt.Analysis.OperatorTheory.StrongOperatorConvergenceIffWeakAndAdjointWanted.tendsto_apply_iff_tendsto_inner_and_tendsto_inner_adjoint_comp`,
  the only declaration of `WantedExt/Analysis/OperatorTheory/StrongOperatorConvergenceIffWeakAndAdjointWanted.lean`
- Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II, problem `ma_proofbench_l2_59`.

Statement to prove, with its name and statement unchanged: for bounded operators $T_n, T$ on a
real or complex Hilbert space, $T_n \to T$ in the strong operator topology if and only if
$T_n \to T$ and $T_n^* T_n \to T^* T$ in the weak operator topology.
